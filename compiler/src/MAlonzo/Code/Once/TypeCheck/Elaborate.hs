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
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.DecEq
import qualified MAlonzo.Code.Once.Internal.Type.Join
import qualified MAlonzo.Code.Once.Internal.Type.Poly
import qualified MAlonzo.Code.Once.Internal.Type.Sub
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Internal.Typing
import qualified MAlonzo.Code.Once.Internal.Typing.Scope
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
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
-- Once.TypeCheck.Elaborate.soundOf
d_soundOf_168 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_InferElabResult_82 -> ()
d_soundOf_168 = erased
-- Once.TypeCheck.Elaborate.VerifiedInferResult
d_VerifiedInferResult_194 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 -> ()
d_VerifiedInferResult_194 = erased
-- Once.TypeCheck.Elaborate.checkSoundOf
d_checkSoundOf_210 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110 -> ()
d_checkSoundOf_210 = erased
-- Once.TypeCheck.Elaborate.VerifiedCheckResult
d_VerifiedCheckResult_240 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_VerifiedCheckResult_240 = erased
-- Once.TypeCheck.Elaborate.GivenElabResult
d_GivenElabResult_260 a0 a1 a2 a3 a4 = ()
data T_GivenElabResult_260
  = C_success_280 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                  MAlonzo.Code.Once.Spec.Context.T_Usage_34
                  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 Integer Integer |
    C_failure_282 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.givenSoundOf
d_givenSoundOf_294 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  T_GivenElabResult_260 -> ()
d_givenSoundOf_294 = erased
-- Once.TypeCheck.Elaborate.VerifiedGivenResult
d_VerifiedGivenResult_332 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 -> ()
d_VerifiedGivenResult_332 = erased
-- Once.TypeCheck.Elaborate.given-infer-dec
d_given'45'infer'45'dec_366 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
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
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'infer'45'dec_366 v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12 v13 v14
  = du_given'45'infer'45'dec_366
      v0 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
du_given'45'infer'45'dec_366 ::
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
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'infer'45'dec_366 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12
  = case coe v11 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
        -> if coe v13
             then case coe v14 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                      -> case coe v12 of
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                             -> if coe v16
                                  then case coe v17 of
                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_success_280 (coe v3) (coe v6)
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
                                                         MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40
                                                         v15
                                                         (coe
                                                            MAlonzo.Code.Once.Internal.Type.Sub.du_'60''58''45'refl_62
                                                            (coe v3))
                                                         v18)
                                                      v7)
                                                   (coe v8) (coe v9))
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Typing.C_d'45'infer_806
                                                   v2 v5 v10 v15 v18)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  else coe
                                         seq (coe v17)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_282
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
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v14)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          C_failure_282
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
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-infer
d_given'45'infer_448 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'infer_448 v0 ~v1 ~v2 v3 v4 v5
  = du_given'45'infer_448 v0 v3 v4 v5
du_given'45'infer_448 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'infer_448 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v4 of
             C_success_98 v6 v7 v8 v9 v10
               -> let v11
                        = coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                            (coe
                               C_failure_282
                               (coe
                                  MAlonzo.Code.Once.TypeCheck.Error.C_ComposeMiddleUndetermined_84))
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v12 v13 v14
                         -> case coe v13 of
                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v15 v16
                                -> case coe v15 of
                                     MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                       -> coe
                                            du_given'45'infer'45'dec_366 (coe v0) (coe v1) (coe v12)
                                            (coe v14) (coe v2) (coe v16) (coe v7) (coe v8) (coe v9)
                                            (coe v10) (coe v5)
                                            (coe
                                               MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__170
                                               (coe v0) (coe v1) (coe v12))
                                            (coe
                                               MAlonzo.Code.Once.Type.Sub.d__'8849'π'63'__10
                                               (coe v16) (coe v2))
                                     _ -> coe v11
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v11)
             C_failure_100 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_282 (coe v6))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.withUnit
d_withUnit_508 ::
  () ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  (MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 -> AgdaAny) -> AgdaAny
d_withUnit_508 ~v0 v1 v2 v3 = du_withUnit_508 v1 v2 v3
du_withUnit_508 ::
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  (MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 -> AgdaAny) -> AgdaAny
du_withUnit_508 v0 v1 v2
  = coe
      du_withUnit'45'aux_514 (coe v0)
      (coe
         MAlonzo.Code.Once.Type.Sub.d__'8849'π'63'__10
         (coe
            MAlonzo.Code.Once.Spec.Grade.C_fin_42
            (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
         (coe v1))
      (coe v2)
-- Once.TypeCheck.Elaborate.withUnit-aux
d_withUnit'45'aux_514 ::
  () ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 -> AgdaAny) -> AgdaAny
d_withUnit'45'aux_514 ~v0 ~v1 v2 v3 v4
  = du_withUnit'45'aux_514 v2 v3 v4
du_withUnit'45'aux_514 ::
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 -> AgdaAny) -> AgdaAny
du_withUnit'45'aux_514 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then case coe v4 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v5 -> coe v2 v5
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe seq (coe v4) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-cata-dec
d_given'45'cata'45'dec_556 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
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
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'cata'45'dec_556 ~v0 v1 ~v2 ~v3 v4 v5 ~v6 v7 ~v8 v9 v10
                           v11 v12 v13 v14
  = du_given'45'cata'45'dec_556 v1 v4 v5 v7 v9 v10 v11 v12 v13 v14
du_given'45'cata'45'dec_556 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'cata'45'dec_556 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
        -> if coe v10
             then coe
                    seq (coe v11)
                    (coe
                       du_withUnit_508
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_failure_282
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                (coe ("cata" :: Data.Text.Text))))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                       (coe v1)
                       (coe
                          (\ v12 ->
                             coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                               (coe
                                  C_success_280 (coe v3)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v4)
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_cata_526 v4
                                     (MAlonzo.Code.Once.Internal.Typing.Scope.d_kinds_144 (coe v0))
                                     v2 v5)
                                  (coe addInt (coe (1 :: Integer)) (coe v6)) (coe v7))
                               (coe
                                  MAlonzo.Code.Once.Internal.Typing.C_d'45'cata_982 v4 v12 v2 v8))))
             else coe
                    seq (coe v11)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          C_failure_282
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                             (coe ("cata" :: Data.Text.Text))))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-cata
d_given'45'cata_624 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'cata_624 v0 v1 ~v2 v3 v4 v5 v6
  = du_given'45'cata_624 v0 v1 v3 v4 v5 v6
du_given'45'cata_624 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'cata_624 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v6 of
             C_success_98 v8 v9 v10 v11 v12
               -> let v13
                        = coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                            (coe
                               C_failure_282
                               (coe
                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                  (coe ("cata" :: Data.Text.Text))))
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
                  coe
                    (case coe v8 of
                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v14 v15 v16
                         -> coe
                              du_given'45'cata'45'dec_556 (coe v1) (coe v3) (coe v4) (coe v16)
                              (coe v9) (coe v10) (coe v11) (coe v12) (coe v7)
                              (coe
                                 MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__230 (coe v0)
                                 (coe v8)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                    (coe
                                       MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v2)
                                       (coe v16))
                                    (coe
                                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
                                    (coe v16)))
                       _ -> coe v13)
             C_failure_100 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_282 (coe v8))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.embedOrSubsume-dec
d_embedOrSubsume'45'dec_690 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_embedOrSubsume'45'dec_690 v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du_embedOrSubsume'45'dec_690 v0 v3 v4 v5 v6 v7 v8 v9 v10
du_embedOrSubsume'45'dec_690 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_embedOrSubsume'45'dec_690 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
        -> if coe v9
             then case coe v10 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_success_126 (coe v1)
                              (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v3 v11 v4)
                              (coe v5) (coe v6))
                           (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'sub_678 v3 v7 v11)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v10)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          C_failure_128
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                             (coe v2) (coe v3)))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.embedOrSubsume
d_embedOrSubsume_734 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_embedOrSubsume_734 v0 ~v1 ~v2 v3 v4
  = du_embedOrSubsume_734 v0 v3 v4
du_embedOrSubsume_734 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_embedOrSubsume_734 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_98 v5 v6 v7 v8 v9
               -> coe
                    du_embedOrSubsume'45'dec_690 (coe v0) (coe v6) (coe v1) (coe v5)
                    (coe v7) (coe v8) (coe v9) (coe v4)
                    (coe
                       MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__170 (coe v0) (coe v5)
                       (coe v1))
             C_failure_100 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v5))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.specId
d_specId_766 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specId_766 ~v0 ~v1 = du_specId_766
du_specId_766 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specId_766
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
      (coe MAlonzo.Code.Once.IR.C_id_20)
-- Once.TypeCheck.Elaborate.specFst
d_specFst_776 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specFst_776 ~v0 ~v1 ~v2 = du_specFst_776
du_specFst_776 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specFst_776
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
      (coe MAlonzo.Code.Once.IR.C_fst_42)
-- Once.TypeCheck.Elaborate.specSnd
d_specSnd_788 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specSnd_788 ~v0 ~v1 ~v2 = du_specSnd_788
du_specSnd_788 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specSnd_788
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
      (coe MAlonzo.Code.Once.IR.C_snd_48)
-- Once.TypeCheck.Elaborate.specInl
d_specInl_800 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specInl_800 ~v0 ~v1 ~v2 = du_specInl_800
du_specInl_800 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specInl_800
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
      (coe MAlonzo.Code.Once.IR.C_inl_54)
-- Once.TypeCheck.Elaborate.specInr
d_specInr_812 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specInr_812 ~v0 ~v1 ~v2 = du_specInr_812
du_specInr_812 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specInr_812
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
      (coe MAlonzo.Code.Once.IR.C_inr_60)
-- Once.TypeCheck.Elaborate.specUnitGen
d_specUnitGen_818 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specUnitGen_818 = coe MAlonzo.Code.Once.Surface.Syntax.C_unit_162
-- Once.TypeCheck.Elaborate.specPair
d_specPair_828 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specPair_828 v0 ~v1 ~v2 = du_specPair_828 v0
du_specPair_828 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specPair_828 v0
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
d_specTerminal_840 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specTerminal_840 ~v0 ~v1 = du_specTerminal_840
du_specTerminal_840 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specTerminal_840
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
      (coe MAlonzo.Code.Once.IR.C_terminal_72)
-- Once.TypeCheck.Elaborate.specInitial
d_specInitial_848 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specInitial_848 ~v0 ~v1 = du_specInitial_848
du_specInitial_848 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specInitial_848
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
      (coe MAlonzo.Code.Once.IR.C_initial_76)
-- Once.TypeCheck.Elaborate.specCurry
d_specCurry_860 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specCurry_860 v0 v1 ~v2 = du_specCurry_860 v0 v1
du_specCurry_860 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specCurry_860 v0 v1
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
d_specApply_874 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specApply_874 v0 v1
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
d_specCompose_888 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specCompose_888 v0 v1 ~v2 = du_specCompose_888 v0 v1
du_specCompose_888 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specCompose_888 v0 v1
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
d_specCase_904 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specCase_904 v0 v1 ~v2 = du_specCase_904 v0 v1
du_specCase_904 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specCase_904 v0 v1
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
d_extract'45'morph'45'aux_930 ::
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
d_extract'45'morph'45'aux_930 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_extract'45'morph'45'aux_930 v4 v8
du_extract'45'morph'45'aux_930 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_extract'45'morph'45'aux_930 v0 v1
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
d_extract'45'morph_950 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extract'45'morph_950 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_extract'45'morph_950 v4 v5 v6 v7
du_extract'45'morph_950 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_extract'45'morph_950 v0 v1 v2 v3
  = coe
      du_extract'45'morph'45'aux_930
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v0)
         (coe
            MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v2))
         (coe v1))
      (coe v3)
-- Once.TypeCheck.Elaborate.WellFormedFView
d_WellFormedFView_960 a0 a1 a2 = ()
data T_WellFormedFView_960
  = C_wfv'45'yes_970 MAlonzo.Code.Once.Spec.Type.T_WFFun_118 |
    C_wfv'45'no_972
-- Once.TypeCheck.Elaborate.inspectWellFormedF
d_inspectWellFormedF_980 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> T_WellFormedFView_960
d_inspectWellFormedF_980 ~v0 v1 v2
  = du_inspectWellFormedF_980 v1 v2
du_inspectWellFormedF_980 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> T_WellFormedFView_960
du_inspectWellFormedF_980 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Functor.Decide.du_wfFun'63'_468 (coe v0)
              (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe C_wfv'45'yes_970 v3
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe C_wfv'45'no_972
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.AppSpine
d_AppSpine_1002 = ()
data T_AppSpine_1002
  = C_mkSpine_1012 MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
                   [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68]
-- Once.TypeCheck.Elaborate.AppSpine.head
d_head_1008 ::
  T_AppSpine_1002 -> MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
d_head_1008 v0
  = case coe v0 of
      C_mkSpine_1012 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.AppSpine.args
d_args_1010 ::
  T_AppSpine_1002 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68]
d_args_1010 v0
  = case coe v0 of
      C_mkSpine_1012 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.spineOf
d_spineOf_1014 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 -> T_AppSpine_1002
d_spineOf_1014 v0
  = coe
      du_go_1022 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.TypeCheck.Elaborate._.go
d_go_1022 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68] ->
  T_AppSpine_1002
d_go_1022 ~v0 v1 v2 = du_go_1022 v1 v2
du_go_1022 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68] ->
  T_AppSpine_1002
du_go_1022 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_70 v2
        -> coe C_mkSpine_1012 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RQualified_72 v2 v3
        -> coe C_mkSpine_1012 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v2
        -> coe C_mkSpine_1012 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v2 v3
        -> coe
             du_go_1022 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3) (coe v1))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 v2 v3
        -> coe C_mkSpine_1012 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_80 v2 v3 v4
        -> coe C_mkSpine_1012 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_82 v2 v3
        -> coe C_mkSpine_1012 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_84 v2 v3 v4 v5 v6
        -> coe C_mkSpine_1012 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_86
        -> coe C_mkSpine_1012 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_88 v2
        -> coe C_mkSpine_1012 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_90 v2 v3 v4
        -> coe C_mkSpine_1012 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_92 v2 v3
        -> coe C_mkSpine_1012 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_94 v2 v3 v4
        -> coe C_mkSpine_1012 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_96 v2
        -> coe C_mkSpine_1012 (coe v0) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.isPolyBuiltin
d_isPolyBuiltin_1108 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_isPolyBuiltin_1108 v0
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
d_matchInferResult_1118 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  T_InferElabResult_82 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_matchInferResult_1118 v0 ~v1 ~v2 v3 v4
  = du_matchInferResult_1118 v0 v3 v4
du_matchInferResult_1118 ::
  Integer ->
  T_InferElabResult_82 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
du_matchInferResult_1118 v0 v1 v2
  = case coe v1 of
      C_success_98 v3 v4 v5 v6 v7
        -> let v8
                 = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__230
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
d_FunProjection_1168 a0 a1 a2 = ()
data T_FunProjection_1168
  = C_isFun_1184 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 Integer Integer |
    C_isEff_1196 MAlonzo.Code.Once.Spec.Grade.T_Purity_40
                 MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68
                 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 Integer Integer |
    C_notFun_1198 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.asFun
d_asFun_1206 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  T_InferElabResult_82 -> T_FunProjection_1168
d_asFun_1206 v0 ~v1 ~v2 v3 = du_asFun_1206 v0 v3
du_asFun_1206 ::
  Integer -> T_InferElabResult_82 -> T_FunProjection_1168
du_asFun_1206 v0 v1
  = case coe v1 of
      C_success_98 v2 v3 v4 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v7
               -> coe
                    C_notFun_1198
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v0)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    C_notFun_1198
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                       (coe (0 :: Integer)) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> coe
                    C_notFun_1198
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                       (coe (0 :: Integer)) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
               -> coe
                    C_notFun_1198
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v0)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v7 v8
               -> coe
                    C_notFun_1198
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
                                         C_isFun_1184 (coe v7) (coe v10) (coe v9) (coe v3) (coe v4)
                                         (coe v5) (coe v6)
                                  MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                    -> case coe v10 of
                                         MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                           -> coe
                                                C_notFun_1198
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                                   (coe v0) (coe v2))
                                         MAlonzo.Code.Once.Spec.Grade.C_One_10
                                           -> coe
                                                C_notFun_1198
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                                   (coe v0) (coe v2))
                                         MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                           -> coe
                                                C_isEff_1196 (coe v11)
                                                (coe MAlonzo.Code.Once.Spec.Grade.C_eg'45'act_70)
                                                (coe v7) (coe v9) (coe v3) (coe v4) (coe v5)
                                                (coe v6)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Spec.Grade.C_eff_44
                             -> case coe v10 of
                                  MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                    -> coe
                                         C_notFun_1198
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                            (coe v0) (coe v2))
                                  MAlonzo.Code.Once.Spec.Grade.C_One_10
                                    -> coe
                                         C_notFun_1198
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                            (coe v0) (coe v2))
                                  MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                    -> coe
                                         C_isEff_1196 (coe v11)
                                         (coe MAlonzo.Code.Once.Spec.Grade.C_eg'45'eff_72) (coe v7)
                                         (coe v9) (coe v3) (coe v4) (coe v5) (coe v6)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v7
               -> coe
                    C_notFun_1198
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v0)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v7 v8
               -> coe
                    C_notFun_1198
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v0)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Int_32
               -> coe
                    C_notFun_1198
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                       (coe (0 :: Integer)) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe
                    C_notFun_1198
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                       (coe (0 :: Integer)) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v2 -> coe C_notFun_1198 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.IntProjection
d_IntProjection_1296 a0 a1 a2 = ()
data T_IntProjection_1296
  = C_isInt_1306 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 Integer Integer |
    C_notInt_1308 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.asInt
d_asInt_1316 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  T_InferElabResult_82 -> T_IntProjection_1296
d_asInt_1316 v0 ~v1 ~v2 v3 = du_asInt_1316 v0 v3
du_asInt_1316 ::
  Integer -> T_InferElabResult_82 -> T_IntProjection_1296
du_asInt_1316 v0 v1
  = case coe v1 of
      C_success_98 v2 v3 v4 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v7
               -> coe
                    C_notInt_1308
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    C_notInt_1308
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                       (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> coe
                    C_notInt_1308
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                       (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
               -> coe
                    C_notInt_1308
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v7 v8
               -> coe
                    C_notInt_1308
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v7 v8 v9
               -> coe
                    C_notInt_1308
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v7
               -> coe
                    C_notInt_1308
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v7 v8
               -> coe
                    C_notInt_1308
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Int_32
               -> coe C_isInt_1306 (coe v3) (coe v4) (coe v5) (coe v6)
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe
                    C_notInt_1308
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                       (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                       (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v2 -> coe C_notInt_1308 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.notNumeric
d_notNumeric_1356 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  T_InferElabResult_82 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
d_notNumeric_1356 v0 ~v1 ~v2 v3 = du_notNumeric_1356 v0 v3
du_notNumeric_1356 ::
  Integer ->
  T_InferElabResult_82 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
du_notNumeric_1356 v0 v1
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
d_decideLeq_1386 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_decideLeq_1386 v0 v1
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
d_inferElab'45'RApp'45'id_1392 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferElab'45'RApp'45'id_1392 ~v0 v1 v2
  = du_inferElab'45'RApp'45'id_1392 v1 v2
du_inferElab'45'RApp'45'id_1392 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferElab'45'RApp'45'id_1392 v0 v1
  = case coe v1 of
      C_success_98 v2 v3 v4 v5 v6
        -> coe
             C_success_98 (coe v2)
             (coe
                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                (MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                   (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v0)))
                (coe
                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v3))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v3 v2
                (coe MAlonzo.Code.Once.IR.C_id_20) v4)
             (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v6)
      C_failure_100 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.isGround-inj₂→¬Ground
d_isGround'45'inj'8322''8594''172'Ground_1412 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_isGround'45'inj'8322''8594''172'Ground_1412 = erased
-- Once.TypeCheck.Elaborate.given-poly-k
d_given'45'poly'45'k_1456 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
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
  MAlonzo.Code.Once.Internal.Type.Poly.T_ArrowSchema_316 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'poly'45'k_1456 ~v0 v1 v2 v3 v4 ~v5 v6 v7 v8 v9 v10 v11
                          v12 ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20
  = du_given'45'poly'45'k_1456
      v1 v2 v3 v4 v6 v7 v8 v9 v10 v11 v12 v17 v18 v19 v20
du_given'45'poly'45'k_1456 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_ArrowSchema_316 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'poly'45'k_1456 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                           v12 v13 v14
  = case coe v14 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
        -> if coe v15
             then case coe v16 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v17
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_success_280 (coe v3)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                 (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v0)))
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
                                    (coe
                                       MAlonzo.Code.Once.Internal.Type.Sub.du_'60''58''45'refl_62
                                       (coe v2))
                                    (coe
                                       MAlonzo.Code.Once.Internal.Type.Sub.du_'60''58''45'refl_62
                                       (coe v3))
                                    v13)
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_406 v1))
                              (coe (0 :: Integer)) (coe (0 :: Integer)))
                           (coe
                              MAlonzo.Code.Once.Internal.Typing.C_d'45'poly_830 v4 v6 v7 v8 v9
                              v10 v11 v12 v17 v13)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v16)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe C_failure_282 (coe v5))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-π
d_given'45'poly'45'π_1542 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
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
  MAlonzo.Code.Once.Internal.Type.Poly.T_ArrowSchema_316 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'poly'45'π_1542 v0 v1 v2 v3 ~v4 v5 v6 v7 v8 v9 v10 v11
                          ~v12 ~v13 ~v14 ~v15 v16 v17 v18 ~v19 v20
  = du_given'45'poly'45'π_1542
      v0 v1 v2 v3 v5 v6 v7 v8 v9 v10 v11 v16 v17 v18 v20
du_given'45'poly'45'π_1542 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_ArrowSchema_316 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'poly'45'π_1542 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                           v12 v13 v14
  = case coe v14 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
        -> if coe v15
             then case coe v16 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v17
                      -> coe
                           du_given'45'poly'45'k_1456 (coe v1) (coe v2) (coe v3)
                           (coe
                              MAlonzo.Code.Once.Internal.Type.Poly.d_substPoly_188 (coe v0)
                              (coe v13) (coe v7))
                           (coe v8) (coe v4) (coe v5) (coe v6) (coe v7) (coe v9) (coe v10)
                           (coe v11) (coe v12) (coe v17)
                           (coe
                              MAlonzo.Code.Once.Type.Rigid.d_kindedInstance'63'_586 (coe v0)
                              (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_kinds_144 (coe v1))
                              (coe v5)
                              (coe
                                 MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.Poly.d_substPoly_188 (coe v0)
                                    (coe v13) (coe v7))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v16)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe C_failure_282 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-m
d_given'45'poly'45'm_1630 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
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
  MAlonzo.Code.Once.Internal.Type.Poly.T_ArrowSchema_316 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'poly'45'm_1630 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                          ~v12 ~v13 ~v14 ~v15 v16 v17 v18 ~v19
  = du_given'45'poly'45'm_1630
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v16 v17 v18
du_given'45'poly'45'm_1630 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
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
  MAlonzo.Code.Once.Internal.Type.Poly.T_ArrowSchema_316 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'poly'45'm_1630 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                           v12 v13 v14
  = case coe v14 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
        -> coe
             du_given'45'poly'45'π_1542 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v12) (coe v13)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   MAlonzo.Code.Once.Type.Instance.du_instantiate'45'sound_1850
                   (coe v0) (coe v7) (coe v3) (coe v15)))
             (coe
                MAlonzo.Code.Once.Type.Sub.d__'8849'π'63'__10 (coe v9) (coe v4))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_282 (coe v5))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-d
d_given'45'poly'45'd_1708 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
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
  MAlonzo.Code.Once.Internal.Type.Poly.T_ArrowSchema_316 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'poly'45'd_1708 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                          ~v12 ~v13 ~v14 ~v15 v16 v17
  = du_given'45'poly'45'd_1708
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v16 v17
du_given'45'poly'45'd_1708 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
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
  MAlonzo.Code.Once.Internal.Type.Poly.T_ArrowSchema_316 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'poly'45'd_1708 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                           v12 v13
  = case coe v13 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
        -> if coe v14
             then case coe v15 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v16
                      -> coe
                           du_given'45'poly'45'm_1630 (coe v0) (coe v1) (coe v2) (coe v3)
                           (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                           (coe v11) (coe v12) (coe v16)
                           (coe
                              MAlonzo.Code.Once.Type.Match.d_instantiate_100 (coe v0) (coe v7)
                              (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v15)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe C_failure_282 (coe v5))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-a
d_given'45'poly'45'a_1772 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'poly'45'a_1772 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 ~v10 ~v11
                          ~v12 v13
  = du_given'45'poly'45'a_1772 v0 v1 v2 v3 v4 v5 v6 v7 v8 v13
du_given'45'poly'45'a_1772 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'poly'45'a_1772 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
        -> case coe v10 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> case coe v12 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                      -> case coe v14 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                             -> coe
                                  du_given'45'poly'45'd_1708 (coe v0) (coe v1) (coe v2) (coe v3)
                                  (coe v4) (coe v5) (coe v6) (coe v11) (coe v13) (coe v15) (coe v7)
                                  (coe v8) (coe v16)
                                  (coe
                                     MAlonzo.Code.Once.Type.Determined.d_codVarsInDom'63'_608
                                     (coe v11) (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_282 (coe v5))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-g
d_given'45'poly'45'g_1838 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'poly'45'g_1838 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 ~v10 ~v11
                          v12 ~v13
  = du_given'45'poly'45'g_1838 v0 v1 v2 v3 v4 v5 v6 v7 v8 v12
du_given'45'poly'45'g_1838 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'poly'45'g_1838 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_282 (coe v5))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
        -> coe
             seq (coe v10)
             (coe
                du_given'45'poly'45'a_1772 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                (coe
                   MAlonzo.Code.Once.Type.Determined.d_arrowSchema'63'_626 (coe v6)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly
d_given'45'poly_1896 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'poly_1896 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 ~v9 v10 ~v11
  = du_given'45'poly_1896 v0 v1 v2 v3 v4 v5 v6 v8 v10
du_given'45'poly_1896 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'poly_1896 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_282 (coe v5))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_282 (coe v5))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> case coe v8 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                      -> case coe v9 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> case coe v11 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                    -> coe
                                         du_given'45'poly'45'g_1838 (coe v0) (coe v1) (coe v2)
                                         (coe v3) (coe v4) (coe v5) (coe v10) (coe v12) (coe v13)
                                         (coe MAlonzo.Code.Once.Type.d_isGround_98 (coe v10))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe C_failure_282 (coe v5))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-res
d_given'45'res_1960 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'res_1960 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v6 of
             C_success_98 v8 v9 v10 v11 v12
               -> coe du_given'45'infer_448 (coe v0) (coe v3) (coe v4) (coe v5)
             C_failure_100 v8
               -> case coe v2 of
                    MAlonzo.Code.Once.Spec.Name.C_canonical_12 v9
                      -> case coe v9 of
                           []
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_282 (coe v8))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (:) v10 v11
                             -> case coe v11 of
                                  []
                                    -> coe
                                         du_given'45'poly_1896 (coe v0) (coe v1) (coe v10) (coe v3)
                                         (coe v4) (coe v8)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupImport_46
                                            (coe
                                               MAlonzo.Code.Once.Internal.Typing.Scope.d_sig_142
                                               (coe v1))
                                            (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupImport_46
                                            (coe
                                               MAlonzo.Code.Once.Internal.Typing.Scope.d_imports_138
                                               (coe v1))
                                            (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupPolyPrefix_76
                                            (coe
                                               MAlonzo.Code.Once.Internal.Typing.Scope.d_polys_140
                                               (coe v1))
                                            (coe v10))
                                  (:) v12 v13
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe C_failure_282 (coe v8))
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-poly-inst-aux
d_checkElabV'45'RVar'45'poly'45'inst'45'aux_2014 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'poly'45'inst'45'aux_2014 ~v0 v1 v2 ~v3 v4
                                                 v5 v6 v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_checkElabV'45'RVar'45'poly'45'inst'45'aux_2014
      v1 v2 v4 v5 v6 v7 v12
du_checkElabV'45'RVar'45'poly'45'inst'45'aux_2014 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RVar'45'poly'45'inst'45'aux_2014 v0 v1 v2 v3 v4 v5
                                                  v6
  = case coe v6 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
        -> if coe v7
             then case coe v8 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_success_126
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                 (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v0)))
                              (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_406 v1)
                              (coe (0 :: Integer)) (coe (0 :: Integer)))
                           (coe
                              MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'poly'45'instantiate_786
                              v3 v4 v5 v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v8)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe C_failure_128 (coe v2))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-poly-ground-aux
d_checkElabV'45'RVar'45'poly'45'ground'45'aux_2068 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'poly'45'ground'45'aux_2068 v0 v1 v2 v3 v4
                                                   v5 v6 v7 ~v8 ~v9 ~v10 v11 ~v12
  = du_checkElabV'45'RVar'45'poly'45'ground'45'aux_2068
      v0 v1 v2 v3 v4 v5 v6 v7 v11
du_checkElabV'45'RVar'45'poly'45'ground'45'aux_2068 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RVar'45'poly'45'ground'45'aux_2068 v0 v1 v2 v3 v4
                                                    v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v4))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
        -> coe
             seq (coe v9)
             (coe
                du_checkElabV'45'RVar'45'poly'45'inst'45'aux_2014 (coe v1) (coe v2)
                (coe v4) (coe v5) (coe v6) (coe v7)
                (coe
                   MAlonzo.Code.Once.Type.Rigid.d_kindedInstance'63'_586 (coe v0)
                   (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_kinds_144 (coe v1))
                   (coe v5) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-poly-check-aux
d_checkElabV'45'RVar'45'poly'45'check'45'aux_2120 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'poly'45'check'45'aux_2120 v0 v1 v2 v3 v4 v5
                                                  ~v6 v7 ~v8 v9 ~v10
  = du_checkElabV'45'RVar'45'poly'45'check'45'aux_2120
      v0 v1 v2 v3 v4 v5 v7 v9
du_checkElabV'45'RVar'45'poly'45'check'45'aux_2120 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RVar'45'poly'45'check'45'aux_2120 v0 v1 v2 v3 v4
                                                   v5 v6 v7
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v4))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v4))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                      -> case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                             -> case coe v10 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                    -> coe
                                         du_checkElabV'45'RVar'45'poly'45'ground'45'aux_2068
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v9)
                                         (coe v11) (coe v12)
                                         (coe MAlonzo.Code.Once.Type.d_isGround_98 (coe v9))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe C_failure_128 (coe v4))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-poly-ground-aux
d_inferElabV'45'RVar'45'poly'45'ground'45'aux_2178 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'poly'45'ground'45'aux_2178 v0 v1 v2 ~v3 ~v4
                                                   v5 v6 ~v7 v8 ~v9
  = du_inferElabV'45'RVar'45'poly'45'ground'45'aux_2178
      v0 v1 v2 v5 v6 v8
du_inferElabV'45'RVar'45'poly'45'ground'45'aux_2178 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'poly'45'ground'45'aux_2178 v0 v1 v2 v3 v4
                                                    v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_98
                (coe
                   MAlonzo.Code.Once.Internal.Type.Poly.d_extractGround_56 (coe v0)
                   (coe v3) (coe v6))
                (coe
                   MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                   (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_406 v2)
                (coe (0 :: Integer)) (coe (0 :: Integer)))
             (coe
                MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'poly'45'instantiate'45'infer_114
                v3 v4
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.du_lookupPoly'8658'lookupPolyPrefix_274
                      (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_polys_140 (coe v1))
                      (coe v2)))
                v6 v6)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> coe
             seq (coe v6)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   C_failure_100
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8 (coe v2)))
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-poly-lookup-aux
d_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2218 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2218 v0 v1 v2 ~v3 ~v4
                                                   v5 ~v6
  = du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2218 v0 v1 v2 v5
du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2218 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2218 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    du_inferElabV'45'RVar'45'poly'45'ground'45'aux_2178 (coe v0)
                    (coe v1) (coe v2) (coe v5) (coe v6)
                    (coe MAlonzo.Code.Once.Type.d_isGround_98 (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8 (coe v2)))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-poly-aux
d_inferElabV'45'RVar'45'poly'45'aux_2248 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'poly'45'aux_2248 v0 v1 v2 ~v3 ~v4
  = du_inferElabV'45'RVar'45'poly'45'aux_2248 v0 v1 v2
du_inferElabV'45'RVar'45'poly'45'aux_2248 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'poly'45'aux_2248 v0 v1 v2
  = coe
      du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2218 (coe v0)
      (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_lookupPoly_10
         (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_polys_140 (coe v1))
         (coe v2))
-- Once.TypeCheck.Elaborate.elabGivenLeaf
d_elabGivenLeaf_2268 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_AppHeadView_306 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elabGivenLeaf_2268 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = d_given'45'res_1960
              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6) in
    coe
      (case coe v5 of
         MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'id_308
           -> coe
                du_withUnit_508
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      C_failure_282
                      (coe
                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                         (coe ("id" :: Data.Text.Text))))
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                (coe v4)
                (coe
                   (\ v8 ->
                      coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_success_280 (coe v3)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                              (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                              (coe MAlonzo.Code.Once.IR.C_id_20))
                           (coe (0 :: Integer)) (coe (0 :: Integer)))
                        (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'id_880 v8)))
         MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'fst_310
           -> let v8
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_282
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                              (coe ("fst" :: Data.Text.Text))))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Once.Spec.Type.C__'42'__22 v9 v10
                     -> coe
                          du_withUnit_508
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                C_failure_282
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                   (coe ("fst" :: Data.Text.Text))))
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                          (coe v4)
                          (coe
                             (\ v11 ->
                                coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     C_success_280 (coe v9)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                        (coe
                                           MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132
                                           (coe v1)))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                        (coe MAlonzo.Code.Once.IR.C_fst_42))
                                     (coe (0 :: Integer)) (coe (0 :: Integer)))
                                  (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'fst_892 v11)))
                   _ -> coe v8)
         MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'snd_312
           -> let v8
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_282
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                              (coe ("snd" :: Data.Text.Text))))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Once.Spec.Type.C__'42'__22 v9 v10
                     -> coe
                          du_withUnit_508
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                C_failure_282
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                   (coe ("snd" :: Data.Text.Text))))
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                          (coe v4)
                          (coe
                             (\ v11 ->
                                coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     C_success_280 (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                        (coe
                                           MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132
                                           (coe v1)))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                        (coe MAlonzo.Code.Once.IR.C_snd_48))
                                     (coe (0 :: Integer)) (coe (0 :: Integer)))
                                  (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'snd_904 v11)))
                   _ -> coe v8)
         MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'terminal_314
           -> coe
                du_withUnit_508
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      C_failure_282
                      (coe
                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                         (coe ("terminal" :: Data.Text.Text))))
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                (coe v4)
                (coe
                   (\ v8 ->
                      coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_success_280 (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                              (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                              (coe MAlonzo.Code.Once.IR.C_terminal_72))
                           (coe (0 :: Integer)) (coe (0 :: Integer)))
                        (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'terminal_914 v8)))
         MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'initial_320
           -> let v8
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_282
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                              (coe ("initial" :: Data.Text.Text))))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Once.Spec.Type.C_Void_20
                     -> coe
                          du_withUnit_508
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                C_failure_282
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                   (coe ("initial" :: Data.Text.Text))))
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                          (coe v4)
                          (coe
                             (\ v9 ->
                                coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     C_success_280 (coe v3)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                        (coe
                                           MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132
                                           (coe v1)))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                        (coe MAlonzo.Code.Once.IR.C_initial_76))
                                     (coe (0 :: Integer)) (coe (0 :: Integer)))
                                  (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'initial_922 v9)))
                   _ -> coe v8)
         _ -> coe v7)
-- Once.TypeCheck.Elaborate.outIR
d_outIR_2342 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_outIR_2342 ~v0 ~v1 v2 ~v3 v4 = du_outIR_2342 v2 v4
du_outIR_2342 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_outIR_2342 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C_Out_110
      (coe
         MAlonzo.Code.Once.IRTy.WF.du_wf'45''8970''8971'_54 (coe v0)
         (coe v1))
-- Once.TypeCheck.Elaborate.inferOutGo
d_inferOutGo_2374 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferOutGo_2374 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11
  = du_inferOutGo_2374 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10
du_inferOutGo_2374 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferOutGo_2374 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_98
                       (coe
                          MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v2)
                          (coe MAlonzo.Code.Once.Spec.Type.C_ν_30 (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                          (MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                             (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v4))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v4
                          (coe MAlonzo.Code.Once.Spec.Type.C_ν_30 (coe v2) (coe v3))
                          (coe du_outIR_2342 (coe v2) (coe v10)) v5)
                       (coe addInt (coe (1 :: Integer)) (coe v6)) (coe v7))
                    (coe
                       MAlonzo.Code.Once.Internal.Typing.C_t'45'Out'45'app'45'infer_368 v2
                       v4 v10 v8)
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
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
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                          (MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                             (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v4))
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
                                (coe du_outIR_2342 (coe v2) (coe v10))
                                (coe MAlonzo.Code.Once.IR.C_fst_42)))
                          v5)
                       (coe addInt (coe (1 :: Integer)) (coe v6)) (coe v7))
                    (coe
                       MAlonzo.Code.Once.Internal.Typing.C_t'45'Out'45'eff'45'app'45'infer_380
                       v2 v4 v10 v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("Out" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferOutAt
d_inferOutAt_2450 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_NuView_260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferOutAt_2450 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9
  = du_inferOutAt_2450 v0 v1 v3 v4 v5 v6 v7 v8 v9
du_inferOutAt_2450 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_NuView_260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferOutAt_2450 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_nu'45'at_268
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v11 v12
               -> coe
                    du_inferOutGo_2374 (coe v0) (coe v1) (coe v11) (coe v12) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7)
                    (coe
                       MAlonzo.Code.Once.Functor.Decide.du_wfFun'63'_468
                       (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_kinds_144 (coe v1))
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_nu'45'other_272
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("Out" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferOutOn
d_inferOutOn_2490 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferOutOn_2490 v0 v1 ~v2 v3 = du_inferOutOn_2490 v0 v1 v3
du_inferOutOn_2490 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferOutOn_2490 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_98 v5 v6 v7 v8 v9
               -> coe
                    du_inferOutAt_2450 (coe v0) (coe v1) (coe v5) (coe v6) (coe v7)
                    (coe v8) (coe v9) (coe v4)
                    (coe MAlonzo.Code.Once.TypeCheck.TargetView.du_nuView_278 (coe v5))
             C_failure_100 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferFstAt
d_inferFstAt_2530 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ProdView_320 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferFstAt_2530 ~v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9
  = du_inferFstAt_2530 v1 v3 v4 v5 v6 v7 v8 v9
du_inferFstAt_2530 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ProdView_320 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferFstAt_2530 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_prod'45'at_328
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_98 (coe v10)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                          (MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                             (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v2))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v2 v1
                          (coe MAlonzo.Code.Once.IR.C_fst_42) v3)
                       (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5))
                    (coe
                       MAlonzo.Code.Once.Internal.Typing.C_t'45'fst'45'app_306 v11 v2 v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_prod'45'other_332
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_38))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferFstOn
d_inferFstOn_2570 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferFstOn_2570 ~v0 v1 ~v2 v3 = du_inferFstOn_2570 v1 v3
du_inferFstOn_2570 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferFstOn_2570 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             C_success_98 v4 v5 v6 v7 v8
               -> coe
                    du_inferFstAt_2530 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7)
                    (coe v8) (coe v3)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.TargetView.du_prodView_338 (coe v4))
             C_failure_100 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferSndAt
d_inferSndAt_2610 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ProdView_320 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferSndAt_2610 ~v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9
  = du_inferSndAt_2610 v1 v3 v4 v5 v6 v7 v8 v9
du_inferSndAt_2610 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ProdView_320 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferSndAt_2610 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_prod'45'at_328
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_98 (coe v11)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                          (MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                             (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v2))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v2 v1
                          (coe MAlonzo.Code.Once.IR.C_snd_48) v3)
                       (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5))
                    (coe
                       MAlonzo.Code.Once.Internal.Typing.C_t'45'snd'45'app_318 v10 v2 v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_prod'45'other_332
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_40))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferSndOn
d_inferSndOn_2650 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferSndOn_2650 ~v0 v1 ~v2 v3 = du_inferSndOn_2650 v1 v3
du_inferSndOn_2650 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferSndOn_2650 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             C_success_98 v4 v5 v6 v7 v8
               -> coe
                    du_inferSndAt_2610 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7)
                    (coe v8) (coe v3)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.TargetView.du_prodView_338 (coe v4))
             C_failure_100 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferApplyAt
d_inferApplyAt_2690 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ApplyView_286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferApplyAt_2690 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9
  = du_inferApplyAt_2690 v0 v1 v3 v4 v5 v6 v7 v8 v9
du_inferApplyAt_2690 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ApplyView_286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferApplyAt_2690 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_apply'45'at_298
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v13 v14
               -> case coe v13 of
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v15 v16 v17
                      -> case coe v16 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v18 v19
                             -> case coe v19 of
                                  MAlonzo.Code.Once.Spec.Grade.C_fin_42 v20
                                    -> case coe v20 of
                                         MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                           -> let v21
                                                    = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__230
                                                        (coe v0) (coe v15) (coe v14) in
                                              coe
                                                (case coe v21 of
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                     -> if coe v22
                                                          then coe
                                                                 seq (coe v23)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe
                                                                       C_success_98 (coe v17)
                                                                       (coe
                                                                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                                          (MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                                                             (coe
                                                                                MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132
                                                                                (coe v1)))
                                                                          (coe
                                                                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                                                                             (coe
                                                                                MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                                             v3))
                                                                       (coe
                                                                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438
                                                                          v3
                                                                          (coe
                                                                             MAlonzo.Code.Once.Spec.Type.C__'42'__22
                                                                             (coe
                                                                                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                                                (coe v15)
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                                                   (coe v19))
                                                                                (coe v17))
                                                                             (coe v15))
                                                                          (coe
                                                                             MAlonzo.Code.Once.IR.C_apply_90)
                                                                          v4)
                                                                       (coe
                                                                          addInt
                                                                          (coe (1 :: Integer))
                                                                          (coe v5))
                                                                       (coe v6))
                                                                    (coe
                                                                       MAlonzo.Code.Once.Internal.Typing.C_t'45'apply'45'app'45'infer_340
                                                                       v15 v3 v7))
                                                          else coe
                                                                 seq (coe v23)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe
                                                                       C_failure_100
                                                                       (coe
                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                          (coe
                                                                             ("apply"
                                                                              ::
                                                                              Data.Text.Text))))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                         MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                           -> let v21
                                                    = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__230
                                                        (coe v0) (coe v15) (coe v14) in
                                              coe
                                                (case coe v21 of
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                     -> if coe v22
                                                          then coe
                                                                 seq (coe v23)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
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
                                                                             (coe v19))
                                                                          (coe v17))
                                                                       (coe
                                                                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                                          (MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                                                             (coe
                                                                                MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132
                                                                                (coe v1)))
                                                                          (coe
                                                                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                                                                             (coe
                                                                                MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                                             v3))
                                                                       (coe
                                                                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438
                                                                          v3
                                                                          (coe
                                                                             MAlonzo.Code.Once.Spec.Type.C__'42'__22
                                                                             (coe
                                                                                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                                                (coe v15)
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                                                   (coe v19))
                                                                                (coe v17))
                                                                             (coe v15))
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
                                                                                         (coe v15))
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                                                         (coe v0)
                                                                                         (coe v17)))
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                                                      (coe v0)
                                                                                      (coe v15)))
                                                                                (coe
                                                                                   MAlonzo.Code.Once.IR.C_apply_90)
                                                                                (coe
                                                                                   MAlonzo.Code.Once.IR.C_fst_42)))
                                                                          v4)
                                                                       (coe
                                                                          addInt
                                                                          (coe (1 :: Integer))
                                                                          (coe v5))
                                                                       (coe v6))
                                                                    (coe
                                                                       MAlonzo.Code.Once.Internal.Typing.C_t'45'apply'45'eff'45'app'45'infer_356
                                                                       v15 v3
                                                                       (coe
                                                                          MAlonzo.Code.Once.Spec.Grade.C_eg'45'act_70)
                                                                       v7))
                                                          else coe
                                                                 seq (coe v23)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe
                                                                       C_failure_100
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
                                  MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                    -> let v20
                                             = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__230
                                                 (coe v0) (coe v15) (coe v14) in
                                       coe
                                         (case coe v20 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                              -> if coe v21
                                                   then coe
                                                          seq (coe v22)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
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
                                                                      (coe v19))
                                                                   (coe v17))
                                                                (coe
                                                                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                                   (MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                                                      (coe
                                                                         MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132
                                                                         (coe v1)))
                                                                   (coe
                                                                      MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                                                                      (coe
                                                                         MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                                      v3))
                                                                (coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438
                                                                   v3
                                                                   (coe
                                                                      MAlonzo.Code.Once.Spec.Type.C__'42'__22
                                                                      (coe
                                                                         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                                         (coe v15)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                            (coe
                                                                               MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                                            (coe v19))
                                                                         (coe v17))
                                                                      (coe v15))
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
                                                                                  (coe v15))
                                                                               (coe
                                                                                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                                                  (coe v0)
                                                                                  (coe v17)))
                                                                            (coe
                                                                               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                                               (coe v0) (coe v15)))
                                                                         (coe
                                                                            MAlonzo.Code.Once.IR.C_apply_90)
                                                                         (coe
                                                                            MAlonzo.Code.Once.IR.C_fst_42)))
                                                                   v4)
                                                                (coe
                                                                   addInt (coe (1 :: Integer))
                                                                   (coe v5))
                                                                (coe v6))
                                                             (coe
                                                                MAlonzo.Code.Once.Internal.Typing.C_t'45'apply'45'eff'45'app'45'infer_356
                                                                v15 v3
                                                                (coe
                                                                   MAlonzo.Code.Once.Spec.Grade.C_eg'45'eff_72)
                                                                v7))
                                                   else coe
                                                          seq (coe v22)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                C_failure_100
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                   (coe
                                                                      ("apply" :: Data.Text.Text))))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_apply'45'other_302
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("apply" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferApplyOn
d_inferApplyOn_2904 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferApplyOn_2904 v0 v1 ~v2 v3 = du_inferApplyOn_2904 v0 v1 v3
du_inferApplyOn_2904 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferApplyOn_2904 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_98 v5 v6 v7 v8 v9
               -> coe
                    du_inferApplyAt_2690 (coe v0) (coe v1) (coe v5) (coe v6) (coe v7)
                    (coe v8) (coe v9) (coe v4)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.TargetView.du_applyView_308 (coe v5))
             C_failure_100 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RPair-aux
d_inferElabV'45'RPair'45'aux_2936 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RPair'45'aux_2936 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_inferElabV'45'RPair'45'aux_2936 v4 v5
du_inferElabV'45'RPair'45'aux_2936 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RPair'45'aux_2936 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             C_success_98 v4 v5 v6 v7 v8
               -> case coe v1 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> case coe v9 of
                           C_success_98 v11 v12 v13 v14 v15
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     C_success_98
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v4) (coe v11))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44 v5
                                        v12)
                                     (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_86 v5 v12 v6 v13)
                                     (coe
                                        MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                        (coe v14))
                                     (coe v15))
                                  (coe
                                     MAlonzo.Code.Once.Internal.Typing.C_t'45'pair_142 v5 v12 v3
                                     v10)
                           C_failure_100 v11
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_100 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RAnnot-aux
d_inferElabV'45'RAnnot'45'aux_2992 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RAnnot'45'aux_2992 v0 ~v1 ~v2 v3 v4
  = du_inferElabV'45'RAnnot'45'aux_2992 v0 v3 v4
du_inferElabV'45'RAnnot'45'aux_2992 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RAnnot'45'aux_2992 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_126 v5 v6 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_98
                       (coe
                          MAlonzo.Code.Once.Internal.Type.d_wk'8320'_12 (coe v0) (coe v1))
                       (coe v5) (coe v6) (coe v7) (coe v8))
                    (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'annot_126 v4)
             C_failure_128 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_100 (coe v5))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RNeg-aux
d_inferElabV'45'RNeg'45'aux_3024 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RNeg'45'aux_3024 v0 ~v1 ~v2 v3
  = du_inferElabV'45'RNeg'45'aux_3024 v0 v3
du_inferElabV'45'RNeg'45'aux_3024 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RNeg'45'aux_3024 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             C_success_98 v4 v5 v6 v7 v8
               -> case coe v4 of
                    MAlonzo.Code.Once.Spec.Type.C_var_16 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v4)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C_Unit_18
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                 (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                                 (coe v4)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C_Void_20
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                 (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                                 (coe v4)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C__'42'__22 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v4)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v4)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v9 v10 v11
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v4)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C_μ_28 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v4)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C_ν_30 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v4)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C_Int_32
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_success_98 (coe v4) (coe v5)
                              (coe MAlonzo.Code.Once.Surface.Syntax.C_neg_308 v6)
                              (coe addInt (coe (1 :: Integer)) (coe v7)) (coe v8))
                           (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'neg_150 v3)
                    MAlonzo.Code.Once.Spec.Type.C_Float_34
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                 (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                                 (coe v4)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_100 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-neg-int-aux
d_checkElabV'45'neg'45'int'45'aux_3112 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'neg'45'int'45'aux_3112 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__170
              (coe v0) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v3) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_126
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                    (coe
                                       MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                                    (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) v7
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_int_194
                                       (MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2))))
                                 (coe (1 :: Integer)) (coe (0 :: Integer)))
                              (coe
                                 MAlonzo.Code.Once.Internal.Typing.C_t'45'sub_678
                                 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Typing.C_t'45'neg_150
                                    (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'int_38))
                                 v7)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_failure_128
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                (coe v3) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElabV-neg-float-aux
d_checkElabV'45'neg'45'float'45'aux_3150 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'neg'45'float'45'aux_3150 v0 v1 v2 v3 v4 v5
  = let v6
          = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__170
              (coe v0) (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v5) in
    coe
      (case coe v6 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
           -> if coe v7
                then case coe v8 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_126
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                    (coe
                                       MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                                    (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) v9
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_float_202
                                       (MAlonzo.Code.Once.Spec.Float.Decimal.d_negate_24
                                          (coe
                                             MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30
                                             (coe v2) (coe v3) (coe v4)))))
                                 (coe (1 :: Integer)) (coe (0 :: Integer)))
                              (coe
                                 MAlonzo.Code.Once.Internal.Typing.C_t'45'sub_678
                                 (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
                                 (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'neg'45'float_160) v9)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v8)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_failure_128
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                (coe v5) (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.inferElabV-RBinOp-aux
d_inferElabV'45'RBinOp'45'aux_3198 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RBinOp'45'aux_3198 v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_inferElabV'45'RBinOp'45'aux_3198 v0 v2 v5 v6
du_inferElabV'45'RBinOp'45'aux_3198 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RBinOp'45'aux_3198 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v4 of
             C_success_98 v6 v7 v8 v9 v10
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Type.C_var_16 v11
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                    (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v6))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C_Unit_18
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                    (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                                    (coe v6))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C_Void_20
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                    (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                                    (coe v6))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C__'42'__22 v11 v12
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                    (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v6))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v11 v12
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                    (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v6))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v11 v12 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                    (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v6))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C_μ_28 v11
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                    (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v6))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C_ν_30 v11 v12
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                    (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v6))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C_Int_32
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                             -> case coe v11 of
                                  C_success_98 v13 v14 v15 v16 v17
                                    -> case coe v13 of
                                         MAlonzo.Code.Once.Spec.Type.C_var_16 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_100
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                         (coe v0) (coe v6) (coe v13))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Type.C_Unit_18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_100
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                         (coe (0 :: Integer)) (coe v6) (coe v13))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Type.C_Void_20
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_100
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                         (coe (0 :: Integer)) (coe v6) (coe v13))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Type.C__'42'__22 v18 v19
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_100
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                         (coe v0) (coe v6) (coe v13))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Type.C__'43'__24 v18 v19
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_100
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                         (coe v0) (coe v6) (coe v13))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v18 v19 v20
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_100
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                         (coe v0) (coe v6) (coe v13))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Type.C_μ_28 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_100
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                         (coe v0) (coe v6) (coe v13))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Type.C_ν_30 v18 v19
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_100
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                         (coe v0) (coe v6) (coe v13))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Type.C_Int_32
                                           -> case coe v1 of
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpAdd_46
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_98 (coe v13)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                             v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_add_212
                                                             v7 v14 v8 v15)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v9) (coe v16))
                                                          (coe v17))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith_228
                                                          v7 v14 v5 v12)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpSub_48
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_98 (coe v13)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                             v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_sub_222
                                                             v7 v14 v8 v15)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v9) (coe v16))
                                                          (coe v17))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith_228
                                                          v7 v14 v5 v12)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMul_50
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_98 (coe v13)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                             v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_mul_232
                                                             v7 v14 v8 v15)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v9) (coe v16))
                                                          (coe v17))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith_228
                                                          v7 v14 v5 v12)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpDiv_52
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_98 (coe v13)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                             v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_div_290
                                                             v7 v14 v8 v15)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v9) (coe v16))
                                                          (coe v17))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith_228
                                                          v7 v14 v5 v12)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMod_54
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_98 (coe v13)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                             v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_mod''_300
                                                             v7 v14 v8 v15)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v9) (coe v16))
                                                          (coe v17))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith_228
                                                          v7 v14 v5 v12)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLt_56
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_98
                                                          (coe
                                                             MAlonzo.Code.Once.Spec.Type.C__'43'__24
                                                             (coe
                                                                MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                                             (coe
                                                                MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                             v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_lt_318
                                                             v7 v14 v8 v15)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v9) (coe v16))
                                                          (coe v17))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'cmp_284
                                                          v7 v14 v5 v12)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLe_58
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_98
                                                          (coe
                                                             MAlonzo.Code.Once.Spec.Type.C__'43'__24
                                                             (coe
                                                                MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                                             (coe
                                                                MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                             v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_le_328
                                                             v7 v14 v8 v15)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v9) (coe v16))
                                                          (coe v17))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'cmp_284
                                                          v7 v14 v5 v12)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGt_60
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_98
                                                          (coe
                                                             MAlonzo.Code.Once.Spec.Type.C__'43'__24
                                                             (coe
                                                                MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                                             (coe
                                                                MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                             v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_gt_338
                                                             v7 v14 v8 v15)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v9) (coe v16))
                                                          (coe v17))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'cmp_284
                                                          v7 v14 v5 v12)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGe_62
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_98
                                                          (coe
                                                             MAlonzo.Code.Once.Spec.Type.C__'43'__24
                                                             (coe
                                                                MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                                             (coe
                                                                MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                             v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_ge_348
                                                             v7 v14 v8 v15)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v9) (coe v16))
                                                          (coe v17))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'cmp_284
                                                          v7 v14 v5 v12)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpEq_64
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_98
                                                          (coe
                                                             MAlonzo.Code.Once.Spec.Type.C__'43'__24
                                                             (coe
                                                                MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                                             (coe
                                                                MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                             v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_eq_358
                                                             v7 v14 v8 v15)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v9) (coe v16))
                                                          (coe v17))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'cmp_284
                                                          v7 v14 v5 v12)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpNe_66
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_98
                                                          (coe
                                                             MAlonzo.Code.Once.Spec.Type.C__'43'__24
                                                             (coe
                                                                MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                                             (coe
                                                                MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                             v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_ne_368
                                                             v7 v14 v8 v15)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v9) (coe v16))
                                                          (coe v17))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'cmp_284
                                                          v7 v14 v5 v12)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Once.Spec.Type.C_Float_34
                                           -> case coe v1 of
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpAdd_46
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_98 (coe v13)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                             v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fadd_242
                                                             v7 v14
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_280
                                                                v8)
                                                             v15)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v9) (coe v16))
                                                          (coe v17))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'il_256
                                                          v7 v14 v5 v12)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpSub_48
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_98 (coe v13)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                             v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fsub_252
                                                             v7 v14
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_280
                                                                v8)
                                                             v15)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v9) (coe v16))
                                                          (coe v17))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'il_256
                                                          v7 v14 v5 v12)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMul_50
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_98 (coe v13)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                             v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fmul_262
                                                             v7 v14
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_280
                                                                v8)
                                                             v15)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v9) (coe v16))
                                                          (coe v17))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'il_256
                                                          v7 v14 v5 v12)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpDiv_52
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_98 (coe v13)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                             v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fdiv_272
                                                             v7 v14
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_280
                                                                v8)
                                                             v15)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v9) (coe v16))
                                                          (coe v17))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'il_256
                                                          v7 v14 v5 v12)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMod_54
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                                (coe (0 :: Integer)) (coe v6)
                                                                (coe v13))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLt_56
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                                (coe (0 :: Integer)) (coe v6)
                                                                (coe v13))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLe_58
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                                (coe (0 :: Integer)) (coe v6)
                                                                (coe v13))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGt_60
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                                (coe (0 :: Integer)) (coe v6)
                                                                (coe v13))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGe_62
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                                (coe (0 :: Integer)) (coe v6)
                                                                (coe v13))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpEq_64
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                                (coe (0 :: Integer)) (coe v6)
                                                                (coe v13))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpNe_66
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                                (coe (0 :: Integer)) (coe v6)
                                                                (coe v13))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  C_failure_100 v13
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            C_failure_100
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                               (coe v13)))
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Spec.Type.C_Float_34
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                             -> case coe v11 of
                                  C_success_98 v13 v14 v15 v16 v17
                                    -> case coe v13 of
                                         MAlonzo.Code.Once.Spec.Type.C_var_16 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_100
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                         (coe v0) (coe v6) (coe v13))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Type.C_Unit_18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_100
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                         (coe (0 :: Integer)) (coe v6) (coe v13))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Type.C_Void_20
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_100
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                         (coe (0 :: Integer)) (coe v6) (coe v13))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Type.C__'42'__22 v18 v19
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_100
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                         (coe v0) (coe v6) (coe v13))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Type.C__'43'__24 v18 v19
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_100
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                         (coe v0) (coe v6) (coe v13))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v18 v19 v20
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_100
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                         (coe v0) (coe v6) (coe v13))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Type.C_μ_28 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_100
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                         (coe v0) (coe v6) (coe v13))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Type.C_ν_30 v18 v19
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_100
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                         (coe v0) (coe v6) (coe v13))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Type.C_Int_32
                                           -> case coe v1 of
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpAdd_46
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_98 (coe v6)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                             v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fadd_242
                                                             v7 v14 v8
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_280
                                                                v15))
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v9) (coe v16))
                                                          (coe v17))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'ir_270
                                                          v7 v14 v5 v12)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpSub_48
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_98 (coe v6)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                             v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fsub_252
                                                             v7 v14 v8
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_280
                                                                v15))
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v9) (coe v16))
                                                          (coe v17))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'ir_270
                                                          v7 v14 v5 v12)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMul_50
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_98 (coe v6)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                             v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fmul_262
                                                             v7 v14 v8
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_280
                                                                v15))
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v9) (coe v16))
                                                          (coe v17))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'ir_270
                                                          v7 v14 v5 v12)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpDiv_52
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_98 (coe v6)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                             v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fdiv_272
                                                             v7 v14 v8
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_280
                                                                v15))
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v9) (coe v16))
                                                          (coe v17))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'ir_270
                                                          v7 v14 v5 v12)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMod_54
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                                (coe (0 :: Integer)) (coe v6)
                                                                (coe v13))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLt_56
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                                (coe (0 :: Integer)) (coe v6)
                                                                (coe v13))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLe_58
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                                (coe (0 :: Integer)) (coe v6)
                                                                (coe v13))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGt_60
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                                (coe (0 :: Integer)) (coe v6)
                                                                (coe v13))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGe_62
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                                (coe (0 :: Integer)) (coe v6)
                                                                (coe v13))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpEq_64
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                                (coe (0 :: Integer)) (coe v6)
                                                                (coe v13))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpNe_66
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                                (coe (0 :: Integer)) (coe v6)
                                                                (coe v13))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Once.Spec.Type.C_Float_34
                                           -> case coe v1 of
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpAdd_46
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_98 (coe v13)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                             v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fadd_242
                                                             v7 v14 v8 v15)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v9) (coe v16))
                                                          (coe v17))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float_242
                                                          v7 v14 v5 v12)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpSub_48
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_98 (coe v13)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                             v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fsub_252
                                                             v7 v14 v8 v15)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v9) (coe v16))
                                                          (coe v17))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float_242
                                                          v7 v14 v5 v12)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMul_50
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_98 (coe v13)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                             v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fmul_262
                                                             v7 v14 v8 v15)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v9) (coe v16))
                                                          (coe v17))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float_242
                                                          v7 v14 v5 v12)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpDiv_52
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_98 (coe v13)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                             v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fdiv_272
                                                             v7 v14 v8 v15)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v9) (coe v16))
                                                          (coe v17))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float_242
                                                          v7 v14 v5 v12)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMod_54
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                                (coe (0 :: Integer))
                                                                (coe
                                                                   MAlonzo.Code.Once.Spec.Type.C_Int_32)
                                                                (coe v13))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLt_56
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                                (coe (0 :: Integer))
                                                                (coe
                                                                   MAlonzo.Code.Once.Spec.Type.C_Int_32)
                                                                (coe v13))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLe_58
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                                (coe (0 :: Integer))
                                                                (coe
                                                                   MAlonzo.Code.Once.Spec.Type.C_Int_32)
                                                                (coe v13))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGt_60
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                                (coe (0 :: Integer))
                                                                (coe
                                                                   MAlonzo.Code.Once.Spec.Type.C_Int_32)
                                                                (coe v13))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGe_62
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                                (coe (0 :: Integer))
                                                                (coe
                                                                   MAlonzo.Code.Once.Spec.Type.C_Int_32)
                                                                (coe v13))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpEq_64
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                                (coe (0 :: Integer))
                                                                (coe
                                                                   MAlonzo.Code.Once.Spec.Type.C_Int_32)
                                                                (coe v13))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpNe_66
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                                (coe (0 :: Integer))
                                                                (coe
                                                                   MAlonzo.Code.Once.Spec.Type.C_Int_32)
                                                                (coe v13))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  C_failure_100 v13
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            C_failure_100
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                               (coe v13)))
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_100 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_100
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86 (coe v6)))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RLet-aux2
d_inferElabV'45'RLet'45'aux2_4234 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RLet'45'aux2_4234 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
                                  ~v9 v10 v11
  = du_inferElabV'45'RLet'45'aux2_4234 v5 v6 v7 v8 v10 v11
du_inferElabV'45'RLet'45'aux2_4234 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RLet'45'aux2_4234 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v6 of
             C_success_98 v8 v9 v10 v11 v12
               -> case coe v9 of
                    MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v14 v15
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_success_98 (coe v8)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44 v15
                                 (coe MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48 v14 v1))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_let''_188 v1 v15 v14 v0 v2 v10)
                              (coe
                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3)
                                 (coe addInt (coe (1 :: Integer)) (coe v11)))
                              (coe v12))
                           (coe
                              MAlonzo.Code.Once.Internal.Typing.C_t'45'let_180 v0 v14 v1 v15 v4
                              v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_100 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-join
d_inferElabV'45'RDestruct'45'join_4336 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
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
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Once.Internal.Type.Join.T_Join'63'_166 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RDestruct'45'join_4336 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22
                                       v23 v24 v25 v26
  = du_inferElabV'45'RDestruct'45'join_4336
      v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23
      v24 v25 v26
du_inferElabV'45'RDestruct'45'join_4336 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Once.Internal.Type.Join.T_Join'63'_166 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RDestruct'45'join_4336 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19
  = case coe v19 of
      MAlonzo.Code.Once.Internal.Type.Join.C_joined_176 v20 v21
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_98 (coe v20)
                (coe
                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44 v2
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__52 (coe v8)
                      (coe v14)))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_case''_156 v2 v8 v14 v7 v13 v0
                   v1 v3
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v6
                      (coe
                         MAlonzo.Code.Once.Internal.Type.Sub.du_'60''58''7580''8658''60''58'_92
                         (coe v6) (coe v20)
                         (coe
                            MAlonzo.Code.Once.Spec.Sub.d_left_166
                            (coe
                               MAlonzo.Code.Once.Internal.Type.Join.du_sound_716 (coe v6)
                               (coe v12) (coe v20) (coe v21))))
                      v9)
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v12
                      (coe
                         MAlonzo.Code.Once.Internal.Type.Sub.du_'60''58''7580''8658''60''58'_92
                         (coe v12) (coe v20)
                         (coe
                            MAlonzo.Code.Once.Spec.Sub.d_right_168
                            (coe
                               MAlonzo.Code.Once.Internal.Type.Join.du_sound_716 (coe v6)
                               (coe v12) (coe v20) (coe v21))))
                      v15))
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                   (coe
                      MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v4)
                      (coe addInt (coe (1 :: Integer)) (coe v10)))
                   (coe addInt (coe (1 :: Integer)) (coe v16)))
                (coe v17))
             (coe
                MAlonzo.Code.Once.Internal.Typing.C_t'45'case_214 v0 v1 v6 v12 v7
                v13 v2 v8 v14 v5 v11 v18
                (coe
                   MAlonzo.Code.Once.Internal.Type.Join.du_sound_716 (coe v6)
                   (coe v12) (coe v20) (coe v21)))
      MAlonzo.Code.Once.Internal.Type.Join.C_apart_178
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseBranchMismatch_48))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-case-join
d_given'45'case'45'join_4450 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30 ->
  MAlonzo.Code.Once.Internal.Type.Join.T_Join'63'_166 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'case'45'join_4450 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
                             v11 v12 v13 v14 v15 v16 v17 v18
  = du_given'45'case'45'join_4450
      v0 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18
du_given'45'case'45'join_4450 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30 ->
  MAlonzo.Code.Once.Internal.Type.Join.T_Join'63'_166 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'case'45'join_4450 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                              v12 v13 v14 v15
  = case coe v15 of
      MAlonzo.Code.Once.Internal.Type.Join.C_joined_176 v16 v17
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_280 (coe v16)
                (coe MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44 v5 v10)
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_copair''_474 v5 v10
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
                         (coe
                            MAlonzo.Code.Once.Internal.Type.Sub.du_'60''58''45'refl_62
                            (coe v1))
                         (coe
                            MAlonzo.Code.Once.Internal.Type.Sub.du_'60''58''7580''8658''60''58'_92
                            (coe v4) (coe v16)
                            (coe
                               MAlonzo.Code.Once.Spec.Sub.d_left_166
                               (coe
                                  MAlonzo.Code.Once.Internal.Type.Join.du_sound_716 (coe v4)
                                  (coe v9) (coe v16) (coe v17))))
                         (MAlonzo.Code.Once.Internal.Type.Sub.d_'8849'π'45'refl_42
                            (coe v3)))
                      v6)
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                      (coe
                         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v2)
                         (coe
                            MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
                         (coe v9))
                      (coe
                         MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40
                         (coe
                            MAlonzo.Code.Once.Internal.Type.Sub.du_'60''58''45'refl_62
                            (coe v2))
                         (coe
                            MAlonzo.Code.Once.Internal.Type.Sub.du_'60''58''7580''8658''60''58'_92
                            (coe v9) (coe v16)
                            (coe
                               MAlonzo.Code.Once.Spec.Sub.d_right_168
                               (coe
                                  MAlonzo.Code.Once.Internal.Type.Join.du_sound_716 (coe v4)
                                  (coe v9) (coe v16) (coe v17))))
                         (MAlonzo.Code.Once.Internal.Type.Sub.d_'8849'π'45'refl_42
                            (coe v3)))
                      v11))
                (coe
                   addInt (coe (1 :: Integer))
                   (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v12)))
                (coe v13))
             (coe
                MAlonzo.Code.Once.Internal.Typing.C_d'45'case_946 v4 v9 v5 v10 v8
                v14
                (coe
                   MAlonzo.Code.Once.Internal.Type.Join.du_sound_716 (coe v4) (coe v9)
                   (coe v16) (coe v17)))
      MAlonzo.Code.Once.Internal.Type.Join.C_apart_178
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_282
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                   (coe v4) (coe v9)))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-auxR
d_inferElabV'45'RDestruct'45'auxR_4554 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
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
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RDestruct'45'auxR_4554 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7 v8 v9 v10 v11 ~v12 v13 v14 v15 v16 v17 v18 ~v19 v20 v21
  = du_inferElabV'45'RDestruct'45'auxR_4554
      v0 v7 v8 v9 v10 v11 v13 v14 v15 v16 v17 v18 v20 v21
du_inferElabV'45'RDestruct'45'auxR_4554 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RDestruct'45'auxR_4554 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11 v12 v13
  = case coe v13 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
        -> case coe v14 of
             C_success_98 v16 v17 v18 v19 v20
               -> case coe v17 of
                    MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v22 v23
                      -> coe
                           du_inferElabV'45'RDestruct'45'join_4336 (coe v1) (coe v2) (coe v3)
                           (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                           (coe v11) (coe v12) (coe v16) (coe v22) (coe v23) (coe v18)
                           (coe v19) (coe v20) (coe v15)
                           (coe
                              MAlonzo.Code.Once.Internal.Type.Join.d_join'63'_640 (coe v0)
                              (coe v7) (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_100 v16
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v14)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.ext-resolved-sem
d_ext'45'resolved'45'sem_4642 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74
d_ext'45'resolved'45'sem_4642 ~v0 ~v1 v2 v3 v4
  = du_ext'45'resolved'45'sem_4642 v2 v3 v4
du_ext'45'resolved'45'sem_4642 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74
du_ext'45'resolved'45'sem_4642 v0 v1 v2
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
d_ext'45'resolved'45'info'45'aux_4648 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_ext'45'resolved'45'info'45'aux_4648 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_ext'45'resolved'45'info'45'aux_4648 v2 v3 v4 v5 v6 v7
du_ext'45'resolved'45'info'45'aux_4648 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
du_ext'45'resolved'45'info'45'aux_4648 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_118 (coe v0)
      (coe du_ext'45'resolved'45'sem_4642 (coe v1) (coe v2) (coe v3))
      (coe v4) (coe v5)
-- Once.TypeCheck.Elaborate.ext-resolved-info
d_ext'45'resolved'45'info_4668 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_ext'45'resolved'45'info_4668 ~v0 ~v1 v2 ~v3 v4 v5 v6 v7
  = du_ext'45'resolved'45'info_4668 v2 v4 v5 v6 v7
du_ext'45'resolved'45'info_4668 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
du_ext'45'resolved'45'info_4668 v0 v1 v2 v3 v4
  = coe
      du_ext'45'resolved'45'info'45'aux_4648 (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.Internal.Type.du_isVoid'63'_58 (coe v0))
      (coe MAlonzo.Code.Once.Internal.Type.du_isUnit'63'_64 (coe v0))
      (coe v3) (coe v4)
-- Once.TypeCheck.Elaborate.resolvedArrowTerm
d_resolvedArrowTerm_4694 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_resolvedArrowTerm_4694 ~v0 v1 v2 ~v3 v4 v5 v6 v7
  = du_resolvedArrowTerm_4694 v1 v2 v4 v5 v6 v7
du_resolvedArrowTerm_4694 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_resolvedArrowTerm_4694 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
      (coe
         MAlonzo.Code.Once.IR.C_SigOp_140 (coe v0) (coe v1)
         (coe
            du_ext'45'resolved'45'info_4668 (coe v1) (coe v2) (coe v3) (coe v4)
            (coe v5)))
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-word
d_inferElabV'45'RResolved'45'word_4718 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'word_4718 ~v0 ~v1 v2 v3 v4 ~v5
  = du_inferElabV'45'RResolved'45'word_4718 v2 v3 v4
du_inferElabV'45'RResolved'45'word_4718 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RResolved'45'word_4718 v0 v1 v2
  = if coe v2
      then coe v1 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      else coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe MAlonzo.Code.Once.Internal.Name.d_showCanonical_6 (coe v0))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-arrow-aux
d_inferElabV'45'RResolved'45'arrow'45'aux_4750 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'arrow'45'aux_4750 v0 v1 v2 v3 v4 v5 v6
                                               ~v7 v8 ~v9 v10 ~v11
  = du_inferElabV'45'RResolved'45'arrow'45'aux_4750
      v0 v1 v2 v3 v4 v5 v6 v8 v10
du_inferElabV'45'RResolved'45'arrow'45'aux_4750 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RResolved'45'arrow'45'aux_4750 v0 v1 v2 v3 v4 v5
                                                v6 v7 v8
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> case coe v8 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
               -> coe
                    du_inferElabV'45'RResolved'45'word_4718 (coe v2)
                    (coe
                       (\ v11 ->
                          coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                            (coe
                               C_success_98
                               (coe
                                  MAlonzo.Code.Once.Internal.Type.d_wk'8320'_12 (coe v0)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v4)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v6))
                                     (coe v5)))
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                  (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                               (coe
                                  du_resolvedArrowTerm_4694 (coe v4) (coe v5) (coe v2) (coe v6)
                                  (coe v9) (coe v10))
                               (coe (0 :: Integer)) (coe (0 :: Integer)))
                            (coe
                               MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'resolved_78
                               (coe
                                  MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v4)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v6))
                                  (coe v5))
                               v3 v11
                               (coe
                                  MAlonzo.Code.Once.Internal.Type.WellFormed.C_con'45'fun_42 v9
                                  v10))))
                    (coe MAlonzo.Code.Once.Internal.Name.d_wordNameB_36 (coe v2))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_100
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                          (coe MAlonzo.Code.Once.Internal.Name.d_showCanonical_6 (coe v2))
                          (coe
                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v4)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v6))
                             (coe v5))))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                   (coe MAlonzo.Code.Once.Internal.Name.d_showCanonical_6 (coe v2))
                   (coe
                      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v6))
                      (coe v5))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.resolvedValueTerm
d_resolvedValueTerm_4808 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_30 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_resolvedValueTerm_4808 ~v0 ~v1 ~v2 v3 v4 v5
  = du_resolvedValueTerm_4808 v3 v4 v5
du_resolvedValueTerm_4808 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_30 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_resolvedValueTerm_4808 v0 v1 v2
  = coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_388 v0 v1 v2
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-value-aux
d_inferElabV'45'RResolved'45'value'45'aux_4824 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'value'45'aux_4824 v0 v1 v2 v3 v4 ~v5
                                               v6 ~v7
  = du_inferElabV'45'RResolved'45'value'45'aux_4824 v0 v1 v2 v3 v4 v6
du_inferElabV'45'RResolved'45'value'45'aux_4824 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RResolved'45'value'45'aux_4824 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             du_inferElabV'45'RResolved'45'word_4718 (coe v2)
             (coe
                (\ v7 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        C_success_98
                        (coe
                           MAlonzo.Code.Once.Internal.Type.d_wk'8320'_12 (coe v0) (coe v4))
                        (coe
                           MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                           (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                        (coe du_resolvedValueTerm_4808 (coe v4) (coe v2) (coe v6))
                        (coe (0 :: Integer)) (coe (0 :: Integer)))
                     (coe
                        MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'resolved_78 v4 v3
                        v7 v6)))
             (coe MAlonzo.Code.Once.Internal.Name.d_wordNameB_36 (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                   (coe MAlonzo.Code.Once.Internal.Name.d_showCanonical_6 (coe v2))
                   (coe v4)))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-def
d_inferElabV'45'RResolved'45'def_4856 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'def_4856 v0 v1 v2 ~v3
  = du_inferElabV'45'RResolved'45'def_4856 v0 v1 v2
du_inferElabV'45'RResolved'45'def_4856 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RResolved'45'def_4856 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Name.C_canonical_12 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        C_failure_100
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                           (coe MAlonzo.Code.Once.Internal.Name.d_showCanonical_6 (coe v2))))
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
           coe
             (case coe v3 of
                (:) v5 v6
                  -> case coe v6 of
                       []
                         -> coe
                              du_inferElabV'45'RResolved'45'own'45'aux_4866 (coe v0) (coe v1)
                              (coe v5)
                              (coe
                                 MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupImport_46
                                 (coe
                                    MAlonzo.Code.Once.Internal.Typing.Scope.d_imports_138 (coe v1))
                                 (coe v5))
                       _ -> coe v4
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-own-aux
d_inferElabV'45'RResolved'45'own'45'aux_4866 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'own'45'aux_4866 v0 v1 v2 ~v3 v4 ~v5
  = du_inferElabV'45'RResolved'45'own'45'aux_4866 v0 v1 v2 v4
du_inferElabV'45'RResolved'45'own'45'aux_4866 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RResolved'45'own'45'aux_4866 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_98
                (coe
                   MAlonzo.Code.Once.Internal.Type.d_wk'8320'_12 (coe v0) (coe v4))
                (coe
                   MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                   (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_closure_396 v2)
                (coe (0 :: Integer)) (coe (0 :: Integer)))
             (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'own_88 v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             du_inferElabV'45'RVar'45'poly'45'aux_2248 (coe v0) (coe v1)
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-aux
d_inferElabV'45'RResolved'45'aux_4876 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'aux_4876 v0 v1 v2 v3 v4 ~v5
  = du_inferElabV'45'RResolved'45'aux_4876 v0 v1 v2 v3 v4
du_inferElabV'45'RResolved'45'aux_4876 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RResolved'45'aux_4876 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> let v6
                 = coe
                     du_inferElabV'45'RResolved'45'value'45'aux_4824 (coe v0) (coe v1)
                     (coe v2) (coe v3) (coe v5)
                     (coe
                        MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52 (coe v5)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v7 v8 v9
                  -> case coe v8 of
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v10 v11
                         -> case coe v10 of
                              MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                -> coe
                                     du_inferElabV'45'RResolved'45'arrow'45'aux_4750 (coe v0)
                                     (coe v1) (coe v2) (coe v3) (coe v7) (coe v9) (coe v11)
                                     (coe
                                        MAlonzo.Code.Once.Functor.Decide.d_isBaseType'63'_8
                                        (coe v7))
                                     (coe
                                        MAlonzo.Code.Once.Functor.Decide.d_isBaseType'63'_8
                                        (coe v9))
                              _ -> coe v6
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v6)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             du_inferElabV'45'RResolved'45'def_4856 (coe v0) (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-import-value-aux
d_inferElabV'45'RVar'45'import'45'value'45'aux_4950 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'import'45'value'45'aux_4950 v0 v1 v2 ~v3 v4
                                                    ~v5 v6 ~v7 v8 ~v9
  = du_inferElabV'45'RVar'45'import'45'value'45'aux_4950
      v0 v1 v2 v4 v6 v8
du_inferElabV'45'RVar'45'import'45'value'45'aux_4950 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'import'45'value'45'aux_4950 v0 v1 v2 v3 v4
                                                     v5
  = case coe v4 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
        -> if coe v6
             then coe
                    seq (coe v7)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          C_failure_100
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8 (coe v2)))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             else coe
                    seq (coe v7)
                    (case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_98
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.d_wk'8320'_12 (coe v0) (coe v3))
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                    (coe
                                       MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_closure_396 v2)
                                 (coe (0 :: Integer)) (coe (0 :: Integer)))
                              (coe
                                 MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'import_98 v3 v8)
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_100
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                                    (coe v2) (coe v3)))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-lookup-aux
d_inferElabV'45'RVar'45'lookup'45'aux_5000 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'lookup'45'aux_5000 v0 v1 v2 v3 ~v4 v5 ~v6
  = du_inferElabV'45'RVar'45'lookup'45'aux_5000 v0 v1 v2 v3 v5
du_inferElabV'45'RVar'45'lookup'45'aux_5000 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'lookup'45'aux_5000 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_success_98 (coe v6) (coe v8)
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.du_svar'8594'expr_568 (coe v9))
                              (coe (0 :: Integer)) (coe (0 :: Integer)))
                           (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'local_68 v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
               -> coe
                    du_inferElabV'45'RVar'45'import'45'value'45'aux_4950 (coe v0)
                    (coe v1) (coe v2) (coe v5)
                    (coe MAlonzo.Code.Once.CanonicalName.d_genWord'63'_22 (coe v2))
                    (coe MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52 (coe v5))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_100
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8 (coe v2)))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-id-failure-aux
d_checkElabV'45'RVar'45'bbc'45'id'45'failure'45'aux_5040 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'id'45'failure'45'aux_5040 v0 v1 v2
                                                         v3
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v4 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe C_failure_128 (coe v3))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe C_failure_128 (coe v3))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> let v9
                               = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__230
                                   (coe v0) (coe v4) (coe v6) in
                         coe
                           (case coe v9 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                -> if coe v10
                                     then coe
                                            seq (coe v11)
                                            (coe
                                               du_withUnit_508
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     C_failure_128
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                        (coe ("id" :: Data.Text.Text))))
                                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                               (coe v8)
                                               (coe
                                                  (\ v12 ->
                                                     coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_126
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                                             (coe
                                                                MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132
                                                                (coe v1)))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                                             (coe MAlonzo.Code.Once.IR.C_id_20))
                                                          (coe (0 :: Integer)) (coe (0 :: Integer)))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'id'45'check_446
                                                          v12))))
                                     else coe
                                            seq (coe v11)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  C_failure_128
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                     (coe ("id" :: Data.Text.Text))))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-fst-failure-aux
d_checkElabV'45'RVar'45'bbc'45'fst'45'failure'45'aux_5132 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'fst'45'failure'45'aux_5132 v0 v1 v2
                                                          v3
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v4 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v3))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v3))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v3))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
               -> case coe v5 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v9 v10
                      -> case coe v9 of
                           MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v3))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Grade.C_One_10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v3))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Grade.C_Many_12
                             -> let v11
                                      = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__230
                                          (coe v0) (coe v7) (coe v6) in
                                coe
                                  (case coe v11 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                       -> if coe v12
                                            then coe
                                                   seq (coe v13)
                                                   (coe
                                                      du_withUnit_508
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            C_failure_128
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                               (coe ("fst" :: Data.Text.Text))))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                      (coe v10)
                                                      (coe
                                                         (\ v14 ->
                                                            coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 C_success_126
                                                                 (coe
                                                                    MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                                                    (coe
                                                                       MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132
                                                                       (coe v1)))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                                                    (coe
                                                                       MAlonzo.Code.Once.IR.C_fst_42))
                                                                 (coe (0 :: Integer))
                                                                 (coe (0 :: Integer)))
                                                              (coe
                                                                 MAlonzo.Code.Once.Internal.Typing.C_t'45'fst'45'check_458
                                                                 v14))))
                                            else coe
                                                   seq (coe v13)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_128
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                            (coe ("fst" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v3))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v7 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v3))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v3))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v3))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_Int_32
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v3))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v3))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-snd-failure-aux
d_checkElabV'45'RVar'45'bbc'45'snd'45'failure'45'aux_5268 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'snd'45'failure'45'aux_5268 v0 v1 v2
                                                          v3
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v4 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v3))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v3))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v3))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
               -> case coe v5 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v9 v10
                      -> case coe v9 of
                           MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v3))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Grade.C_One_10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v3))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Grade.C_Many_12
                             -> let v11
                                      = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__230
                                          (coe v0) (coe v8) (coe v6) in
                                coe
                                  (case coe v11 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                       -> if coe v12
                                            then coe
                                                   seq (coe v13)
                                                   (coe
                                                      du_withUnit_508
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            C_failure_128
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                               (coe ("snd" :: Data.Text.Text))))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                      (coe v10)
                                                      (coe
                                                         (\ v14 ->
                                                            coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 C_success_126
                                                                 (coe
                                                                    MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                                                    (coe
                                                                       MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132
                                                                       (coe v1)))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                                                    (coe
                                                                       MAlonzo.Code.Once.IR.C_snd_48))
                                                                 (coe (0 :: Integer))
                                                                 (coe (0 :: Integer)))
                                                              (coe
                                                                 MAlonzo.Code.Once.Internal.Typing.C_t'45'snd'45'check_470
                                                                 v14))))
                                            else coe
                                                   seq (coe v13)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_128
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                            (coe ("snd" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v3))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v7 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v3))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v3))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v3))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_Int_32
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v3))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v3))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-terminal-failure-aux
d_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_5404 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_5404 ~v0
                                                               v1 v2 v3
  = du_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_5404
      v1 v2 v3
du_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_5404 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_5404 v0
                                                                v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe
                           seq (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_128 (coe v2))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           seq (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_128 (coe v2))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> case coe v5 of
                           MAlonzo.Code.Once.Spec.Type.C_Unit_18
                             -> coe
                                  du_withUnit_508
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_128
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("terminal" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                  (coe v7)
                                  (coe
                                     (\ v8 ->
                                        coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                          (coe
                                             C_success_126
                                             (coe
                                                MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132
                                                   (coe v0)))
                                             (coe
                                                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                                (coe MAlonzo.Code.Once.IR.C_terminal_72))
                                             (coe (0 :: Integer)) (coe (0 :: Integer)))
                                          (coe
                                             MAlonzo.Code.Once.Internal.Typing.C_t'45'terminal'45'morph'45'check_480
                                             v8)))
                           MAlonzo.Code.Once.Spec.Type.C_var_16 v8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C_Void_20
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C__'43'__24 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v8 v9 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C_μ_28 v8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C_ν_30 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C_Int_32
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C_Float_34
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-initial-failure-aux
d_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_5508 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_5508 ~v0
                                                              v1 v2 v3
  = du_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_5508
      v1 v2 v3
du_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_5508 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_5508 v0
                                                               v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v3 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> case coe v4 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v6 v7
                      -> case coe v6 of
                           MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Grade.C_One_10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Grade.C_Many_12
                             -> coe
                                  du_withUnit_508
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_128
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("initial" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                  (coe v7)
                                  (coe
                                     (\ v8 ->
                                        coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                          (coe
                                             C_success_126
                                             (coe
                                                MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132
                                                   (coe v0)))
                                             (coe
                                                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                                (coe MAlonzo.Code.Once.IR.C_initial_76))
                                             (coe (0 :: Integer)) (coe (0 :: Integer)))
                                          (coe
                                             MAlonzo.Code.Once.Internal.Typing.C_t'45'initial'45'morph'45'check_490
                                             v8)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v6 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_Int_32
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_128 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inl-failure-aux
d_checkElabV'45'RVar'45'bbc'45'inl'45'failure'45'aux_5612 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'inl'45'failure'45'aux_5612 v0 v1 v2
                                                          v3
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v4 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe
                           seq (coe v6)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_128 (coe v3))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           seq (coe v6)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_128 (coe v3))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> case coe v6 of
                           MAlonzo.Code.Once.Spec.Type.C__'43'__24 v9 v10
                             -> let v11
                                      = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__230
                                          (coe v0) (coe v4) (coe v9) in
                                coe
                                  (case coe v11 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                       -> if coe v12
                                            then coe
                                                   seq (coe v13)
                                                   (coe
                                                      du_withUnit_508
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            C_failure_128
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                               (coe ("inl" :: Data.Text.Text))))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                      (coe v8)
                                                      (coe
                                                         (\ v14 ->
                                                            coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 C_success_126
                                                                 (coe
                                                                    MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                                                    (coe
                                                                       MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132
                                                                       (coe v1)))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                                                    (coe
                                                                       MAlonzo.Code.Once.IR.C_inl_54))
                                                                 (coe (0 :: Integer))
                                                                 (coe (0 :: Integer)))
                                                              (coe
                                                                 MAlonzo.Code.Once.Internal.Typing.C_t'45'inl'45'morph'45'check_502
                                                                 v14))))
                                            else coe
                                                   seq (coe v13)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_128
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                            (coe ("inl" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.Spec.Type.C_var_16 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v3))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C_Unit_18
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v3))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C_Void_20
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v3))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 v9 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v3))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v9 v10 v11
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v3))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C_μ_28 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v3))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C_ν_30 v9 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v3))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C_Int_32
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v3))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C_Float_34
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v3))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inr-failure-aux
d_checkElabV'45'RVar'45'bbc'45'inr'45'failure'45'aux_5748 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'inr'45'failure'45'aux_5748 v0 v1 v2
                                                          v3
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v4 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe
                           seq (coe v6)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_128 (coe v3))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           seq (coe v6)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_128 (coe v3))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> case coe v6 of
                           MAlonzo.Code.Once.Spec.Type.C__'43'__24 v9 v10
                             -> let v11
                                      = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__230
                                          (coe v0) (coe v4) (coe v10) in
                                coe
                                  (case coe v11 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                       -> if coe v12
                                            then coe
                                                   seq (coe v13)
                                                   (coe
                                                      du_withUnit_508
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            C_failure_128
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                               (coe ("inr" :: Data.Text.Text))))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                      (coe v8)
                                                      (coe
                                                         (\ v14 ->
                                                            coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 C_success_126
                                                                 (coe
                                                                    MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                                                    (coe
                                                                       MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132
                                                                       (coe v1)))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                                                    (coe
                                                                       MAlonzo.Code.Once.IR.C_inr_60))
                                                                 (coe (0 :: Integer))
                                                                 (coe (0 :: Integer)))
                                                              (coe
                                                                 MAlonzo.Code.Once.Internal.Typing.C_t'45'inr'45'morph'45'check_514
                                                                 v14))))
                                            else coe
                                                   seq (coe v13)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_128
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                            (coe ("inr" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.Spec.Type.C_var_16 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v3))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C_Unit_18
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v3))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C_Void_20
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v3))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 v9 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v3))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v9 v10 v11
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v3))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C_μ_28 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v3))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C_ν_30 v9 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v3))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C_Int_32
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v3))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Type.C_Float_34
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v3))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_128 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-id-aux
d_checkElabV'45'RVar'45'bbc'45'id'45'aux_5882 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'id'45'aux_5882 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v4 of
             C_success_98 v6 v7 v8 v9 v10
               -> coe du_embedOrSubsume_734 (coe v0) (coe v2) (coe v3)
             C_failure_100 v6
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'id'45'failure'45'aux_5040 (coe v0)
                    (coe v1) (coe v2) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-fst-aux
d_checkElabV'45'RVar'45'bbc'45'fst'45'aux_5902 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'fst'45'aux_5902 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v4 of
             C_success_98 v6 v7 v8 v9 v10
               -> coe du_embedOrSubsume_734 (coe v0) (coe v2) (coe v3)
             C_failure_100 v6
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'fst'45'failure'45'aux_5132 (coe v0)
                    (coe v1) (coe v2) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-snd-aux
d_checkElabV'45'RVar'45'bbc'45'snd'45'aux_5922 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'snd'45'aux_5922 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v4 of
             C_success_98 v6 v7 v8 v9 v10
               -> coe du_embedOrSubsume_734 (coe v0) (coe v2) (coe v3)
             C_failure_100 v6
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'snd'45'failure'45'aux_5268 (coe v0)
                    (coe v1) (coe v2) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-terminal-aux
d_checkElabV'45'RVar'45'bbc'45'terminal'45'aux_5942 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'terminal'45'aux_5942 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v4 of
             C_success_98 v6 v7 v8 v9 v10
               -> coe du_embedOrSubsume_734 (coe v0) (coe v2) (coe v3)
             C_failure_100 v6
               -> coe
                    du_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_5404
                    (coe v1) (coe v2) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-initial-aux
d_checkElabV'45'RVar'45'bbc'45'initial'45'aux_5962 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'initial'45'aux_5962 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v4 of
             C_success_98 v6 v7 v8 v9 v10
               -> coe du_embedOrSubsume_734 (coe v0) (coe v2) (coe v3)
             C_failure_100 v6
               -> coe
                    du_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_5508
                    (coe v1) (coe v2) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inl-aux
d_checkElabV'45'RVar'45'bbc'45'inl'45'aux_5982 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'inl'45'aux_5982 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v4 of
             C_success_98 v6 v7 v8 v9 v10
               -> coe du_embedOrSubsume_734 (coe v0) (coe v2) (coe v3)
             C_failure_100 v6
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'inl'45'failure'45'aux_5612 (coe v0)
                    (coe v1) (coe v2) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inr-aux
d_checkElabV'45'RVar'45'bbc'45'inr'45'aux_6002 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'inr'45'aux_6002 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v4 of
             C_success_98 v6 v7 v8 v9 v10
               -> coe du_embedOrSubsume_734 (coe v0) (coe v2) (coe v3)
             C_failure_100 v6
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'inr'45'failure'45'aux_5748 (coe v0)
                    (coe v1) (coe v2) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-dispatch
d_inferElabV'45'RResolved'45'dispatch_6022 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_640 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'dispatch_6022 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'id_642
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("id" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'fst_644
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("fst" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'snd_646
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("snd" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'terminal_648
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("terminal" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'initial_650
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("initial" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inl_652
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("inl" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inr_654
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("inr" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'unit_656
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                (coe
                   MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                   (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_162)
                (coe (0 :: Integer)) (coe (0 :: Integer)))
             (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'unit'45'var_56)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'other_660 v5
        -> coe
             du_inferElabV'45'RResolved'45'aux_4876 (coe v0) (coe v1) (coe v2)
             (coe v5)
             (coe
                MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupImport_46
                (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_sig_142 (coe v1))
                (coe MAlonzo.Code.Once.Internal.Name.d_showCanonical_6 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RResolved-other
d_checkElabV'45'RResolved'45'other_6068 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RResolved'45'other_6068 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v5 of
             C_success_98 v7 v8 v9 v10 v11
               -> coe du_embedOrSubsume_734 (coe v0) (coe v3) (coe v4)
             C_failure_100 v7
               -> case coe v2 of
                    MAlonzo.Code.Once.Spec.Name.C_canonical_12 v8
                      -> case coe v8 of
                           []
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_128 (coe v7))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (:) v9 v10
                             -> case coe v10 of
                                  []
                                    -> coe
                                         du_checkElabV'45'RVar'45'poly'45'check'45'aux_2120 (coe v0)
                                         (coe v1) (coe v9) (coe v3) (coe v7)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupImport_46
                                            (coe
                                               MAlonzo.Code.Once.Internal.Typing.Scope.d_sig_142
                                               (coe v1))
                                            (coe v9))
                                         (coe
                                            MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupImport_46
                                            (coe
                                               MAlonzo.Code.Once.Internal.Typing.Scope.d_imports_138
                                               (coe v1))
                                            (coe v9))
                                         (coe
                                            MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupPolyPrefix_76
                                            (coe
                                               MAlonzo.Code.Once.Internal.Typing.Scope.d_polys_140
                                               (coe v1))
                                            (coe v9))
                                  (:) v11 v12
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe C_failure_128 (coe v7))
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RResolved-dispatch
d_checkElabV'45'RResolved'45'dispatch_6106 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_640 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RResolved'45'dispatch_6106 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'id_642
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'id'45'aux_5882 (coe v0) (coe v1)
             (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'fst_644
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'fst'45'aux_5902 (coe v0) (coe v1)
             (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'snd_646
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'snd'45'aux_5922 (coe v0) (coe v1)
             (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'terminal_648
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'terminal'45'aux_5942 (coe v0)
             (coe v1) (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'initial_650
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'initial'45'aux_5962 (coe v0)
             (coe v1) (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inl_652
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'inl'45'aux_5982 (coe v0) (coe v1)
             (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inr_654
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'inr'45'aux_6002 (coe v0) (coe v1)
             (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'unit_656
        -> coe du_embedOrSubsume_734 (coe v0) (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'other_660 v7
        -> coe
             d_checkElabV'45'RResolved'45'other_6068 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-other-aux
d_checkElabV'45'RVar'45'bbc'45'other'45'aux_6176 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'other'45'aux_6176 v0 ~v1 ~v2 v3 v4
  = du_checkElabV'45'RVar'45'bbc'45'other'45'aux_6176 v0 v3 v4
du_checkElabV'45'RVar'45'bbc'45'other'45'aux_6176 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RVar'45'bbc'45'other'45'aux_6176 v0 v1 v2
  = coe du_embedOrSubsume_734 (coe v0) (coe v1) (coe v2)
-- Once.TypeCheck.Elaborate.checkElabV-RFloat-aux
d_checkElabV'45'RFloat'45'aux_6198 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RFloat'45'aux_6198 v0 v1 v2 v3 v4 v5
  = let v6
          = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__170
              (coe v0) (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v5) in
    coe
      (case coe v6 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
           -> if coe v7
                then case coe v8 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_126
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                    (coe
                                       MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                                    (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) v9
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_float_202
                                       (MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30
                                          (coe v2) (coe v3) (coe v4))))
                                 (coe (0 :: Integer)) (coe (0 :: Integer)))
                              (coe
                                 MAlonzo.Code.Once.Internal.Typing.C_t'45'sub_678
                                 (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
                                 (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'float_48) v9)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v8)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_failure_128
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                (coe v5) (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.inferElabV-RFloat-aux
d_inferElabV'45'RFloat'45'aux_6246 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RFloat'45'aux_6246 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
         (coe
            MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
            (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v0)))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_float_202
            (MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30
               (coe v1) (coe v2) (coe v3)))
         (coe (0 :: Integer)) (coe (0 :: Integer)))
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'float_48)
-- Once.TypeCheck.Elaborate.checkPair
d_checkPair_6266 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkPair_6266 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_failure_128
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                    (coe ("pair" :: Data.Text.Text))))
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v8
                  -> case coe v8 of
                       MAlonzo.Code.Once.Spec.Name.C_canonical_12 v9
                         -> case coe v9 of
                              (:) v10 v11
                                -> case coe v10 of
                                     l | (==) l ("Generators" :: Data.Text.Text) ->
                                         case coe v11 of
                                           (:) v12 v13
                                             -> case coe v12 of
                                                  l | (==) l ("pair" :: Data.Text.Text) ->
                                                      case coe v13 of
                                                        []
                                                          -> coe
                                                               d_checkPairOn_6278 (coe v0) (coe v1)
                                                               (coe v7) (coe v3) (coe v4)
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.TargetView.du_pairTarget_168
                                                                  (coe v4))
                                                        _ -> coe v5
                                                  _ -> coe v5
                                           _ -> coe v5
                                     _ -> coe v5
                              _ -> coe v5
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v5
         _ -> coe v5)
-- Once.TypeCheck.Elaborate.checkPairOn
d_checkPairOn_6278 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_PairTarget_146 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkPairOn_6278 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_pair'45'at_158
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v10 v11 v12
               -> case coe v11 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v13 v14
                      -> case coe v12 of
                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 v15 v16
                             -> let v17
                                      = d_checkElabV_6580
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
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                       -> case coe v18 of
                                            C_success_126 v20 v21 v22 v23
                                              -> let v24
                                                       = d_checkElabV_6580
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
                                                   (case coe v24 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                        -> case coe v25 of
                                                             C_success_126 v27 v28 v29 v30
                                                               -> coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe
                                                                       C_success_126
                                                                       (coe
                                                                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                                          v20 v27)
                                                                       (coe
                                                                          MAlonzo.Code.Once.Surface.Syntax.C_fork''_492
                                                                          v20 v27 v21 v28)
                                                                       (coe
                                                                          addInt
                                                                          (coe (1 :: Integer))
                                                                          (coe
                                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                             (coe v22) (coe v29)))
                                                                       (coe v30))
                                                                    (coe
                                                                       MAlonzo.Code.Once.Internal.Typing.C_t'45'pair'45'morph'45'check_598
                                                                       v20 v27 v19 v26)
                                                             C_failure_128 v27
                                                               -> coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe v25)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            C_failure_128 v20
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe v18)
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_pair'45'other_162
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_128
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("pair" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkPairLit
d_checkPairLit_6292 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkPairLit_6292 v0 v1 v2 v3 v4 v5
  = let v6 = d_checkElabV_6580 (coe v0) (coe v1) (coe v2) (coe v4) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> case coe v7 of
                C_success_126 v9 v10 v11 v12
                  -> let v13
                           = d_checkElabV_6580 (coe v0) (coe v1) (coe v3) (coe v5) in
                     coe
                       (case coe v13 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                            -> case coe v14 of
                                 C_success_126 v16 v17 v18 v19
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           C_success_126
                                           (coe
                                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                              v9 v16)
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_pair_86 v9 v16 v10
                                              v17)
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v11)
                                              (coe v18))
                                           (coe v19))
                                        (coe
                                           MAlonzo.Code.Once.Internal.Typing.C_t'45'pair'45'lit'45'check_716
                                           v9 v16 v8 v15)
                                 C_failure_128 v16
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v14)
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_128 v9
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkCase
d_checkCase_6304 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCase_6304 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_failure_128
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                    (coe ("case" :: Data.Text.Text))))
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v8
                  -> case coe v8 of
                       MAlonzo.Code.Once.Spec.Name.C_canonical_12 v9
                         -> case coe v9 of
                              (:) v10 v11
                                -> case coe v10 of
                                     l | (==) l ("Generators" :: Data.Text.Text) ->
                                         case coe v11 of
                                           (:) v12 v13
                                             -> case coe v12 of
                                                  l | (==) l ("case" :: Data.Text.Text) ->
                                                      case coe v13 of
                                                        []
                                                          -> coe
                                                               d_checkCaseOn_6316 (coe v0) (coe v1)
                                                               (coe v7) (coe v3) (coe v4)
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.TargetView.du_caseTarget_202
                                                                  (coe v4))
                                                        _ -> coe v5
                                                  _ -> coe v5
                                           _ -> coe v5
                                     _ -> coe v5
                              _ -> coe v5
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v5
         _ -> coe v5)
-- Once.TypeCheck.Elaborate.checkCaseOn
d_checkCaseOn_6316 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_CaseTarget_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCaseOn_6316 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_case'45'at_192
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v10 v11 v12
               -> case coe v10 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v13 v14
                      -> case coe v11 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v15 v16
                             -> coe
                                  d_checkCaseGo_6334 (coe v0) (coe v1) (coe v2) (coe v3) (coe v13)
                                  (coe v14) (coe v12) (coe v16)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_case'45'other_196
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_128
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("case" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCaseGo
d_checkCaseGo_6334 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCaseGo_6334 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = d_checkElabV_6580
              (coe v0) (coe v1) (coe v2)
              (coe
                 MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v4)
                 (coe
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v7))
                 (coe v6)) in
    coe
      (case coe v8 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
           -> case coe v9 of
                C_success_126 v11 v12 v13 v14
                  -> let v15
                           = d_checkElabV_6580
                               (coe v0) (coe v1) (coe v3)
                               (coe
                                  MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v7))
                                  (coe v6)) in
                     coe
                       (case coe v15 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                            -> case coe v16 of
                                 C_success_126 v18 v19 v20 v21
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           C_success_126
                                           (coe
                                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                              v11 v18)
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_copair''_474 v11
                                              v18 v12 v19)
                                           (coe
                                              addInt (coe (1 :: Integer))
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v13)
                                                 (coe v20)))
                                           (coe v14))
                                        (coe
                                           MAlonzo.Code.Once.Internal.Typing.C_t'45'case'45'copair'45'check_578
                                           v11 v18 v10 v17)
                                 C_failure_128 v18
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_128 v11
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkCompose
d_checkCompose_6346 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCompose_6346 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_failure_128
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                    (coe ("compose" :: Data.Text.Text))))
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v8
                  -> case coe v8 of
                       MAlonzo.Code.Once.Spec.Name.C_canonical_12 v9
                         -> case coe v9 of
                              (:) v10 v11
                                -> case coe v10 of
                                     l | (==) l ("Generators" :: Data.Text.Text) ->
                                         case coe v11 of
                                           (:) v12 v13
                                             -> case coe v12 of
                                                  l | (==) l ("compose" :: Data.Text.Text) ->
                                                      case coe v13 of
                                                        []
                                                          -> coe
                                                               d_checkComposeOn_6358 (coe v0)
                                                               (coe v1) (coe v7) (coe v3) (coe v4)
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.TargetView.du_arrowTarget_234
                                                                  (coe v4))
                                                        _ -> coe v5
                                                  _ -> coe v5
                                           _ -> coe v5
                                     _ -> coe v5
                              _ -> coe v5
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v5
         _ -> coe v5)
-- Once.TypeCheck.Elaborate.checkComposeOn
d_checkComposeOn_6358 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ArrowTarget_214 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkComposeOn_6358 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_arrow'45'at_224
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v9 v10 v11
               -> case coe v10 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v12 v13
                      -> coe
                           d_checkCompose'45'g_6400 (coe v0) (coe v1) (coe v2) (coe v3)
                           (coe v9) (coe v11) (coe v13)
                           (coe
                              d_elabGivenV_6370 (coe v0) (coe v1) (coe v3) (coe v9) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_arrow'45'other_228
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_128
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("compose" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.elabGivenV
d_elabGivenV_6370 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elabGivenV_6370 v0 v1 v2 v3 v4
  = let v5
          = coe
              du_given'45'infer_448 (coe v0) (coe v3) (coe v4)
              (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v2)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v6
           -> coe
                d_elabGivenLeaf_2268 (coe v0) (coe v1) (coe v6) (coe v3) (coe v4)
                (coe
                   MAlonzo.Code.Once.Internal.Typing.Scope.d_classifyAppHeadView_352
                   (coe v2))
                (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v2))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v6 v7
           -> coe
                d_elabGivenApp_6384 (coe v0) (coe v1) (coe v6) (coe v7) (coe v3)
                (coe v4)
                (coe
                   MAlonzo.Code.Once.Internal.Typing.Scope.d_classifyAppHeadView_352
                   (coe v6))
                (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v2))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 v6 v7
           -> let v8
                    = d_inferElabV_6570
                        (coe v0)
                        (coe
                           MAlonzo.Code.Once.Internal.Typing.Scope.du_extendNamedCtx_150
                           (coe v1) (coe v6) (coe v3))
                        (coe v7) in
              coe
                (case coe v8 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                     -> case coe v9 of
                          C_success_98 v11 v12 v13 v14 v15
                            -> case coe v12 of
                                 MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v17 v18
                                   -> let v19
                                            = d_decideLeq_1386
                                                (coe v17)
                                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) in
                                      coe
                                        (case coe v19 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
                                             -> coe
                                                  du_withUnit_508
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        C_failure_282
                                                        (coe
                                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                           (coe ("lambda" :: Data.Text.Text))))
                                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                  (coe v4)
                                                  (coe
                                                     (\ v21 ->
                                                        coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             C_success_280 (coe v11) (coe v18)
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_lam_38
                                                                v17 v13)
                                                             (coe
                                                                addInt (coe (1 :: Integer))
                                                                (coe v14))
                                                             (coe v15))
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Typing.C_d'45'lam_850
                                                             v17 v21 v10)))
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                             -> coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     C_failure_282
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Error.C_UsageViolation_78
                                                        (coe v6)
                                                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                        (coe v17)))
                                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          C_failure_100 v11
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe C_failure_282 (coe v11))
                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v5)
-- Once.TypeCheck.Elaborate.elabGivenApp
d_elabGivenApp_6384 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_AppHeadView_306 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elabGivenApp_6384 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = coe du_given'45'infer_448 (coe v0) (coe v4) (coe v5) (coe v7) in
    coe
      (case coe v6 of
         MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'cata_328
           -> let v9
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_282
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                              (coe ("cata" :: Data.Text.Text))))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Once.Spec.Type.C_μ_28 v10
                     -> let v11
                              = coe
                                  MAlonzo.Code.Once.Functor.Decide.du_wfFun'63'_468
                                  (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_kinds_144 (coe v1))
                                  (coe v10) in
                        coe
                          (case coe v11 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                               -> coe
                                    du_given'45'cata_624 (coe v0) (coe v1) (coe v10) (coe v5)
                                    (coe v12) (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v3))
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       C_failure_282
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                          (coe ("cata" :: Data.Text.Text))))
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> coe v9)
         MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'pair'45'applied_336
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v10 v11
                  -> let v12
                           = d_elabGivenV_6370
                               (coe v0) (coe v1) (coe v11) (coe v4) (coe v5) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                            -> case coe v13 of
                                 C_success_280 v15 v16 v17 v18 v19
                                   -> let v20
                                            = d_elabGivenV_6370
                                                (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) in
                                      coe
                                        (case coe v20 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                             -> case coe v21 of
                                                  C_success_280 v23 v24 v25 v26 v27
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            C_success_280
                                                            (coe
                                                               MAlonzo.Code.Once.Spec.Type.C__'42'__22
                                                               (coe v15) (coe v23))
                                                            (coe
                                                               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                               v16 v24)
                                                            (coe
                                                               MAlonzo.Code.Once.Surface.Syntax.C_fork''_492
                                                               v16 v24 v17 v25)
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                  (coe v18) (coe v26)))
                                                            (coe v27))
                                                         (coe
                                                            MAlonzo.Code.Once.Internal.Typing.C_d'45'pair_966
                                                            v16 v24 v14 v22)
                                                  C_failure_282 v23
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v21)
                                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 C_failure_282 v15
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v8
         MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'compose'45'applied_340
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v10 v11
                  -> let v12
                           = d_elabGivenV_6370 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                            -> case coe v13 of
                                 C_success_280 v15 v16 v17 v18 v19
                                   -> let v20
                                            = d_elabGivenV_6370
                                                (coe v0) (coe v1) (coe v11) (coe v15) (coe v5) in
                                      coe
                                        (case coe v20 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                             -> case coe v21 of
                                                  C_success_280 v23 v24 v25 v26 v27
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            C_success_280 (coe v23)
                                                            (coe
                                                               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                               v24
                                                               (coe
                                                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                                                                  (coe
                                                                     MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                                  v16))
                                                            (coe
                                                               MAlonzo.Code.Once.Surface.Syntax.C_comp''_456
                                                               v24 v16 v15 v25 v17)
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                  (coe v26) (coe v18)))
                                                            (coe v27))
                                                         (coe
                                                            MAlonzo.Code.Once.Internal.Typing.C_d'45'compose_870
                                                            v15 v24 v16 v14 v22)
                                                  C_failure_282 v23
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v21)
                                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 C_failure_282 v15
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v8
         MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'case'45'applied_344
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v10 v11
                  -> let v12
                           = coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                               (coe
                                  C_failure_282
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                     (coe ("case" :: Data.Text.Text))))
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
                     coe
                       (case coe v4 of
                          MAlonzo.Code.Once.Spec.Type.C__'43'__24 v13 v14
                            -> let v15
                                     = d_elabGivenV_6370
                                         (coe v0) (coe v1) (coe v11) (coe v13) (coe v5) in
                               coe
                                 (case coe v15 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                      -> case coe v16 of
                                           C_success_280 v18 v19 v20 v21 v22
                                             -> let v23
                                                      = d_elabGivenV_6370
                                                          (coe v0) (coe v1) (coe v3) (coe v14)
                                                          (coe v5) in
                                                coe
                                                  (case coe v23 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                       -> case coe v24 of
                                                            C_success_280 v26 v27 v28 v29 v30
                                                              -> coe
                                                                   du_given'45'case'45'join_4450
                                                                   (coe v0) (coe v13) (coe v14)
                                                                   (coe v5) (coe v18) (coe v19)
                                                                   (coe v20) (coe v21) (coe v17)
                                                                   (coe v26) (coe v27) (coe v28)
                                                                   (coe v29) (coe v30) (coe v25)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Internal.Type.Join.d_join'63'_640
                                                                      (coe v0) (coe v18) (coe v26))
                                                            C_failure_282 v26
                                                              -> coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe v24)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           C_failure_282 v18
                                             -> coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v16)
                                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> coe v12)
                _ -> coe v8
         _ -> coe v8)
-- Once.TypeCheck.Elaborate.checkCompose-g
d_checkCompose'45'g_6400 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCompose'45'g_6400 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
        -> case coe v8 of
             C_success_280 v10 v11 v12 v13 v14
               -> let v15
                        = d_checkElabV_6580
                            (coe v0) (coe v1) (coe v2)
                            (coe
                               MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v10)
                               (coe
                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v6))
                               (coe v5)) in
                  coe
                    (case coe v15 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                         -> case coe v16 of
                              C_success_126 v18 v19 v20 v21
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_success_126
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44 v18
                                           (coe
                                              MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v11))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_comp''_456 v18 v11 v10
                                           v19 v12)
                                        (coe
                                           addInt (coe (1 :: Integer))
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v20)
                                              (coe v13)))
                                        (coe v21))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Typing.C_t'45'compose'45'check'45'g_534
                                        v10 v18 v11 v9 v17)
                              C_failure_128 v18
                                -> coe
                                     d_checkCompose'45'f_6416 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe v4) (coe v5) (coe v6)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             C_failure_282 v10
               -> coe
                    d_checkCompose'45'f_6416 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCompose-f
d_checkCompose'45'f_6416 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCompose'45'f_6416 v0 v1 v2 v3 v4 v5 v6
  = let v7 = d_inferElabV_6570 (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v7 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
           -> let v10
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_128
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_ComposeMiddleUndetermined_84))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v8 of
                   C_success_98 v11 v12 v13 v14 v15
                     -> case coe v11 of
                          MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v16 v17 v18
                            -> case coe v17 of
                                 MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v19 v20
                                   -> case coe v19 of
                                        MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                          -> let v21
                                                   = coe
                                                       MAlonzo.Code.Once.Type.Sub.du_arr'45'aux_30
                                                       (coe
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                                          (coe
                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                             erased))
                                                       (coe
                                                          MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__170
                                                          (coe v0) (coe v16) (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__170
                                                          (coe v0) (coe v18) (coe v5))
                                                       (coe
                                                          MAlonzo.Code.Once.Type.Sub.d__'8849'π'63'__10
                                                          (coe v20) (coe v6)) in
                                             coe
                                               (case coe v21 of
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                    -> if coe v22
                                                         then case coe v23 of
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v24
                                                                  -> let v25
                                                                           = d_checkElabV_6580
                                                                               (coe v0) (coe v1)
                                                                               (coe v3)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                                                  (coe v4)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                                     (coe v19)
                                                                                     (coe v6))
                                                                                  (coe v16)) in
                                                                     coe
                                                                       (case coe v25 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                            -> case coe v26 of
                                                                                 C_success_126 v28 v29 v30 v31
                                                                                   -> coe
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                        (coe
                                                                                           C_success_126
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                                                              v12
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                                                                                                 v19
                                                                                                 v28))
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Surface.Syntax.C_comp''_456
                                                                                              v12
                                                                                              v28
                                                                                              v16
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                                                                                                 v11
                                                                                                 v24
                                                                                                 v13)
                                                                                              v29)
                                                                                           (coe
                                                                                              addInt
                                                                                              (coe
                                                                                                 (1 ::
                                                                                                    Integer))
                                                                                              (coe
                                                                                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                 (coe
                                                                                                    v14)
                                                                                                 (coe
                                                                                                    v30)))
                                                                                           (coe
                                                                                              v31))
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Internal.Typing.C_t'45'compose'45'check'45'f_558
                                                                                           v16 v18
                                                                                           v20 v12
                                                                                           v28 v9
                                                                                           v24 v27)
                                                                                 C_failure_128 v28
                                                                                   -> coe
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                        (coe v26)
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         else coe
                                                                seq (coe v23)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      C_failure_128
                                                                      (coe
                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_ComposeMiddleUndetermined_84))
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> coe v10
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> coe v10
                   _ -> coe v10)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkCurry
d_checkCurry_6426 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCurry_6426 v0 v1 v2 v3
  = coe
      d_checkCurryOn_6436 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.TypeCheck.TargetView.du_curryTarget_132 (coe v3))
-- Once.TypeCheck.Elaborate.checkCurryOn
d_checkCurryOn_6436 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_CurryTarget_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCurryOn_6436 v0 v1 v2 v3 v4
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
                                             = d_checkElabV_6580
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
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                              -> case coe v21 of
                                                   C_success_126 v23 v24 v25 v26
                                                     -> coe
                                                          du_withUnit_508
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                C_failure_128
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                   (coe
                                                                      ("curry" :: Data.Text.Text))))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                          (coe v14)
                                                          (coe
                                                             (\ v27 ->
                                                                coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe
                                                                     C_success_126 (coe v23)
                                                                     (coe
                                                                        MAlonzo.Code.Once.Surface.Syntax.C_curry''_510
                                                                        v24)
                                                                     (coe
                                                                        addInt (coe (1 :: Integer))
                                                                        (coe v25))
                                                                     (coe v26))
                                                                  (coe
                                                                     MAlonzo.Code.Once.Internal.Typing.C_t'45'curry'45'check_618
                                                                     v27 v22)))
                                                   C_failure_128 v23
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe v21)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_curry'45'other_126
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_128
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("curry" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferOut
d_inferOut_6444 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferOut_6444 v0 v1 v2
  = coe
      du_inferOutOn_2490 (coe v0) (coe v1)
      (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.Elaborate.checkIn
d_checkIn_6454 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkIn_6454 v0 v1 v2 v3
  = coe
      d_checkInOn_6464 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.TypeCheck.TargetView.du_inTarget_102 (coe v3))
-- Once.TypeCheck.Elaborate.checkInOn
d_checkInOn_6464 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_InTarget_86 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkInOn_6464 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_in'45'at_92
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v6
               -> coe
                    du_checkInGo_6476 (coe v0) (coe v1) (coe v2) (coe v6)
                    (coe
                       MAlonzo.Code.Once.Functor.Decide.du_wfFun'63'_468
                       (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_kinds_144 (coe v1))
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_in'45'other_96
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_128
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("In" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkInGo
d_checkInGo_6476 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkInGo_6476 v0 v1 v2 v3 v4 ~v5
  = du_checkInGo_6476 v0 v1 v2 v3 v4
du_checkInGo_6476 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkInGo_6476 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> let v6
                 = d_checkElabV_6580
                     (coe v0) (coe v1) (coe v2)
                     (coe
                        MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v3)
                        (coe MAlonzo.Code.Once.Spec.Type.C_μ_28 (coe v3))) in
           coe
             (case coe v6 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                  -> case coe v7 of
                       C_success_126 v9 v10 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_126
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                    (MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                       (coe
                                          MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132
                                          (coe v1)))
                                    (coe
                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v9))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v9
                                    (coe
                                       MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v3)
                                       (coe MAlonzo.Code.Once.Spec.Type.C_μ_28 (coe v3)))
                                    (coe
                                       MAlonzo.Code.Once.IR.C_In_94
                                       (coe
                                          MAlonzo.Code.Once.IRTy.WF.du_wf'45''8970''8971'_54
                                          (coe v3) (coe v5)))
                                    v10)
                                 (coe addInt (coe (1 :: Integer)) (coe v11)) (coe v12))
                              (coe
                                 MAlonzo.Code.Once.Internal.Typing.C_t'45'In'45'app'45'check_726 v9
                                 v5 v8)
                       C_failure_128 v9
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_128
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("In" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCata
d_checkCata_6486 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCata_6486 v0 v1 v2 v3
  = coe
      d_checkCataOn_6496 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.TypeCheck.TargetView.du_cataTarget_28 (coe v3))
-- Once.TypeCheck.Elaborate.checkCataOn
d_checkCataOn_6496 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_CataTarget_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCataOn_6496 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_cata'45'at_18
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v8 v9 v10
               -> case coe v8 of
                    MAlonzo.Code.Once.Spec.Type.C_μ_28 v11
                      -> case coe v9 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v12 v13
                             -> coe
                                  du_checkCataGo_6512 (coe v0) (coe v1) (coe v2) (coe v11) (coe v10)
                                  (coe v13)
                                  (coe
                                     MAlonzo.Code.Once.Functor.Decide.du_wfFun'63'_468
                                     (coe
                                        MAlonzo.Code.Once.Internal.Typing.Scope.d_kinds_144
                                        (coe v1))
                                     (coe v11))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_cata'45'other_22
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_128
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("cata" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCataGo
d_checkCataGo_6512 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCataGo_6512 v0 v1 v2 v3 v4 v5 v6 ~v7
  = du_checkCataGo_6512 v0 v1 v2 v3 v4 v5 v6
du_checkCataGo_6512 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkCataGo_6512 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> let v8
                 = d_checkElabV_6580
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
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                  -> case coe v9 of
                       C_success_126 v11 v12 v13 v14
                         -> coe
                              du_withUnit_508
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    C_failure_128
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                       (coe ("cata" :: Data.Text.Text))))
                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              (coe v5)
                              (coe
                                 (\ v15 ->
                                    coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                      (coe
                                         C_success_126
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v11)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_cata_526 v11
                                            (MAlonzo.Code.Once.Internal.Typing.Scope.d_kinds_144
                                               (coe v1))
                                            v7 v12)
                                         (coe addInt (coe (1 :: Integer)) (coe v13)) (coe v14))
                                      (coe
                                         MAlonzo.Code.Once.Internal.Typing.C_t'45'cata'45'check_634
                                         v11 v15 v7 v10)))
                       C_failure_128 v11
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_128
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("cata" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkAna
d_checkAna_6522 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkAna_6522 v0 v1 v2 v3
  = coe
      d_checkAnaOn_6532 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.TypeCheck.TargetView.du_anaTarget_66 (coe v3))
-- Once.TypeCheck.Elaborate.checkAnaOn
d_checkAnaOn_6532 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_AnaTarget_38 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkAnaOn_6532 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_loop'45'at_46
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v7 v8 v9
               -> coe
                    du_checkLoop_6562
                    (coe
                       d_checkElabV_6580 (coe v0) (coe v1) (coe v2)
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
                                  du_checkAnaGo_6550 (coe v0) (coe v1) (coe v2) (coe v15) (coe v10)
                                  (coe v14) (coe v16) (coe v9)
                                  (coe
                                     MAlonzo.Code.Once.Functor.Decide.du_wfFun'63'_468
                                     (coe
                                        MAlonzo.Code.Once.Internal.Typing.Scope.d_kinds_144
                                        (coe v1))
                                     (coe v15))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_ana'45'other_60
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_128
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("ana" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkAnaGo
d_checkAnaGo_6550 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkAnaGo_6550 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9
  = du_checkAnaGo_6550 v0 v1 v2 v3 v4 v5 v6 v7 v8
du_checkAnaGo_6550 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkAnaGo_6550 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> let v10
                 = d_checkElabV_6580
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
             (case coe v10 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                  -> case coe v11 of
                       C_success_126 v13 v14 v15 v16
                         -> coe
                              du_withUnit_508
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    C_failure_128
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                       (coe ("ana" :: Data.Text.Text))))
                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              (coe v5)
                              (coe
                                 (\ v17 ->
                                    coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                      (coe
                                         C_success_126
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v13)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_ana_544 v13
                                            (MAlonzo.Code.Once.Internal.Typing.Scope.d_kinds_144
                                               (coe v1))
                                            v9 v14)
                                         (coe addInt (coe (1 :: Integer)) (coe v15)) (coe v16))
                                      (coe
                                         MAlonzo.Code.Once.Internal.Typing.C_t'45'ana'45'check_654
                                         v13 v17 v7 v9 v12)))
                       C_failure_128 v13
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_128
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("ana" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkLoop
d_checkLoop_6562 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkLoop_6562 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_checkLoop_6562 v5
du_checkLoop_6562 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkLoop_6562 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v1 of
             C_success_126 v3 v4 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_126
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v3)
                       (coe MAlonzo.Code.Once.Surface.Syntax.C_loop_556 v3 v4)
                       (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v6))
                    (coe
                       MAlonzo.Code.Once.Internal.Typing.C_t'45'loop'45'check_666 v3 v2)
             C_failure_128 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV
d_inferElabV_6570 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV_6570 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_70 v3
        -> coe
             du_inferElabV'45'RVar'45'lookup'45'aux_5000 (coe v0) (coe v1)
             (coe v3)
             (coe
                MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupLocal_258 (coe v0)
                (coe v1) (coe v3))
             (coe
                MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupImport_46
                (coe
                   MAlonzo.Code.Once.Internal.Typing.Scope.d_imports_138 (coe v1))
                (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RQualified_72 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundQualified_14 (coe v3)
                   (coe v4)))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v3
        -> coe
             d_inferElabV'45'RResolved'45'dispatch_6022 (coe v0) (coe v1)
             (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_692 (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v3 v4
        -> coe
             du_inferElabV'45'RApp'45'dispatch_6708 (coe v0) (coe v1) (coe v3)
             (coe v4)
             (coe
                MAlonzo.Code.Once.Internal.Typing.Scope.d_classifyAppHeadView_352
                (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_LambdaInInferMode_24))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_80 v3 v4 v5
        -> coe
             du_inferElabV'45'RLet'45'aux_6638 (coe v0) (coe v1) (coe v3)
             (coe v5) (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_82 v3 v4
        -> coe
             du_inferElabV'45'RPair'45'aux_2936
             (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v3))
             (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_84 v3 v4 v5 v6 v7
        -> coe
             du_inferElabV'45'RDestruct'45'aux_6654 (coe v0) (coe v1) (coe v4)
             (coe v5) (coe v6) (coe v7)
             (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_86
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                (coe
                   MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                   (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_162)
                (coe (0 :: Integer)) (coe (0 :: Integer)))
             (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'unit_52)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_88 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                (coe
                   MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                   (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_int_194 v3)
                (coe (0 :: Integer)) (coe (0 :: Integer)))
             (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'int_38)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_90 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
                (coe
                   MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                   (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_float_202
                   (MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30
                      (coe v3) (coe v4) (coe v5)))
                (coe (0 :: Integer)) (coe (0 :: Integer)))
             (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'float_48)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_92 v3 v4
        -> coe
             du_inferElabV'45'RAnnot'45'aux_2992 (coe v0) (coe v4)
             (coe
                d_checkElabV_6580 (coe v0) (coe v1) (coe v3)
                (coe
                   MAlonzo.Code.Once.Internal.Type.d_wk'8320'_12 (coe v0) (coe v4)))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_94 v3 v4 v5
        -> coe
             du_inferElabV'45'RBinOp'45'aux_3198 (coe v0) (coe v3)
             (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v4))
             (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_96 v3
        -> coe
             d_inferElabV'45'neg'45'dispatch_6608 (coe v0) (coe v1) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV
d_checkElabV_6580 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV_6580 v0 v1 v2 v3
  = coe du_checkElabV'45'wf_6590 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.TypeCheck.Elaborate.checkElabV-wf
d_checkElabV'45'wf_6590 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'wf_6590 v0 v1 ~v2 v3 v4
  = du_checkElabV'45'wf_6590 v0 v1 v3 v4
du_checkElabV'45'wf_6590 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'wf_6590 v0 v1 v2 v3
  = let v4
          = coe
              du_embedOrSubsume_734 (coe v0) (coe v3)
              (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v2)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_70 v5
           -> let v6
                    = coe
                        du_inferElabV'45'RVar'45'lookup'45'aux_5000 (coe v0) (coe v1)
                        (coe v5)
                        (coe
                           MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupLocal'45'go_172
                           (coe v0)
                           (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1))
                           (coe v5)
                           (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_named_134 (coe v1))
                           (coe
                              MAlonzo.Code.Once.Internal.Typing.Scope.d_debruijn_136 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupImport_46
                           (coe
                              MAlonzo.Code.Once.Internal.Typing.Scope.d_imports_138 (coe v1))
                           (coe v5)) in
              coe
                (case coe v6 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                     -> case coe v7 of
                          C_success_98 v9 v10 v11 v12 v13
                            -> coe du_embedOrSubsume_734 (coe v0) (coe v3) (coe v6)
                          C_failure_100 v9
                            -> coe
                                 du_checkElabV'45'RVar'45'bbc'45'other'45'aux_6176 (coe v0) (coe v3)
                                 (coe v6)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v5
           -> coe
                d_checkElabV'45'RResolved'45'dispatch_6106 (coe v0) (coe v1)
                (coe v5) (coe v3)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_692 (coe v5))
                (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v2))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v5 v6
           -> coe
                du_checkElabV'45'RApp'45'dispatch_6722 (coe v0) (coe v1) (coe v5)
                (coe v6) (coe v3)
                (coe
                   MAlonzo.Code.Once.Internal.Typing.Scope.d_classifyAppHeadView_352
                   (coe v5))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 v5 v6
           -> let v7
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_128
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_LambdaRequiresFunctionType_26))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v8 v9 v10
                     -> case coe v9 of
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v11 v12
                            -> let v13
                                     = d_checkElabV_6580
                                         (coe v0)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Typing.Scope.du_extendNamedCtx_150
                                            (coe v1) (coe v5) (coe v8))
                                         (coe v6) (coe v10) in
                               coe
                                 (case coe v13 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                      -> case coe v14 of
                                           C_success_126 v16 v17 v18 v19
                                             -> case coe v16 of
                                                  MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v21 v22
                                                    -> let v23
                                                             = d_decideLeq_1386
                                                                 (coe v21) (coe v11) in
                                                       coe
                                                         (case coe v23 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v24
                                                              -> coe
                                                                   du_withUnit_508
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe
                                                                         C_failure_128
                                                                         (coe
                                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                            (coe
                                                                               ("lambda"
                                                                                ::
                                                                                Data.Text.Text))))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                   (coe v12)
                                                                   (coe
                                                                      (\ v25 ->
                                                                         coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe
                                                                              C_success_126
                                                                              (coe v22)
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Surface.Syntax.C_lam_38
                                                                                 v21 v17)
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (1 :: Integer))
                                                                                 (coe v18))
                                                                              (coe v19))
                                                                           (coe
                                                                              MAlonzo.Code.Once.Internal.Typing.C_t'45'lam_700
                                                                              v21 v25 v15)))
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              -> coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      C_failure_128
                                                                      (coe
                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_UsageViolation_78
                                                                         (coe v5) (coe v11)
                                                                         (coe v21)))
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           C_failure_128 v16
                                             -> coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v14)
                                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> coe v7)
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_82 v5 v6
           -> coe
                d_checkElabV'45'RPair'45'aux_6754 (coe v0) (coe v1) (coe v5)
                (coe v6) (coe v3) (coe du_classifyRPairTarget_60 (coe v3))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_88 v5
           -> coe
                d_checkElabV'45'RInt'45'aux_6742 (coe v0) (coe v1) (coe v5)
                (coe v3)
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_90 v5 v6 v7
           -> coe
                d_checkElabV'45'RFloat'45'aux_6198 (coe v0) (coe v1) (coe v5)
                (coe v6) (coe v7) (coe v3)
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_96 v5
           -> coe
                d_checkElabV'45'neg'45'dispatch_6626 (coe v0) (coe v1) (coe v5)
                (coe v3) (coe d_negOperandView_150 (coe v5))
         _ -> coe v4)
-- Once.TypeCheck.Elaborate.inferElabV-RApp-other
d_inferElabV'45'RApp'45'other_6600 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RApp'45'other_6600 v0 v1 v2 v3
  = coe
      du_inferElabV'45'RApp'45'other'45'aux_6696 (coe v0) (coe v1)
      (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.Internal.Typing.Scope.d_classifyAppHead_582
         (coe v2))
-- Once.TypeCheck.Elaborate.inferElabV-neg-dispatch
d_inferElabV'45'neg'45'dispatch_6608 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'neg'45'dispatch_6608 v0 v1 v2
  = coe
      d_inferElabV'45'neg'45'aux_6616 (coe v0) (coe v1) (coe v2)
      (coe d_negOperandView_150 (coe v2))
-- Once.TypeCheck.Elaborate.inferElabV-neg-aux
d_inferElabV'45'neg'45'aux_6616 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_NegOperandView_130 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'neg'45'aux_6616 v0 v1 v2 v3
  = case coe v3 of
      C_nov'45'int_134
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_88 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                          (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_int_194
                          (MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v5)))
                       (coe (1 :: Integer)) (coe (0 :: Integer)))
                    (coe
                       MAlonzo.Code.Once.Internal.Typing.C_t'45'neg_150
                       (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'int_38))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'float_142
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_90 v7 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                          (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_float_202
                          (MAlonzo.Code.Once.Spec.Float.Decimal.d_negate_24
                             (coe
                                MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30 (coe v7)
                                (coe v8) (coe v9))))
                       (coe (1 :: Integer)) (coe (0 :: Integer)))
                    (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'neg'45'float_160)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'other_146
        -> coe
             du_inferElabV'45'RNeg'45'aux_3024 (coe v0)
             (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-neg-dispatch
d_checkElabV'45'neg'45'dispatch_6626 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_NegOperandView_130 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'neg'45'dispatch_6626 v0 v1 v2 v3 v4
  = case coe v4 of
      C_nov'45'int_134
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_88 v6
               -> coe
                    d_checkElabV'45'neg'45'int'45'aux_3112 (coe v0) (coe v1) (coe v6)
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'float_142
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_90 v8 v9 v10
               -> coe
                    d_checkElabV'45'neg'45'float'45'aux_3150 (coe v0) (coe v1) (coe v8)
                    (coe v9) (coe v10) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'other_146
        -> coe
             du_embedOrSubsume_734 (coe v0) (coe v3)
             (coe
                du_inferElabV'45'RNeg'45'aux_3024 (coe v0)
                (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RLet-aux
d_inferElabV'45'RLet'45'aux_6638 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RLet'45'aux_6638 v0 v1 v2 ~v3 v4 v5
  = du_inferElabV'45'RLet'45'aux_6638 v0 v1 v2 v4 v5
du_inferElabV'45'RLet'45'aux_6638 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RLet'45'aux_6638 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v5 of
             C_success_98 v7 v8 v9 v10 v11
               -> coe
                    du_inferElabV'45'RLet'45'aux2_4234 (coe v7) (coe v8) (coe v9)
                    (coe v10) (coe v6)
                    (coe
                       d_inferElabV_6570 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Internal.Typing.Scope.du_extendNamedCtx_150
                          (coe v1) (coe v2) (coe v7))
                       (coe v3))
             C_failure_100 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-aux
d_inferElabV'45'RDestruct'45'aux_6654 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RDestruct'45'aux_6654 v0 v1 ~v2 v3 v4 v5 v6 v7
  = du_inferElabV'45'RDestruct'45'aux_6654 v0 v1 v3 v4 v5 v6 v7
du_inferElabV'45'RDestruct'45'aux_6654 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RDestruct'45'aux_6654 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
        -> case coe v7 of
             C_success_98 v9 v10 v11 v12 v13
               -> case coe v9 of
                    MAlonzo.Code.Once.Spec.Type.C_var_16 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C_Unit_18
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C_Void_20
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C__'42'__22 v14 v15
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v14 v15
                      -> coe
                           du_inferElabV'45'RDestruct'45'auxL_6684 (coe v0) (coe v1) (coe v4)
                           (coe v5) (coe v14) (coe v15) (coe v10) (coe v11) (coe v12) (coe v8)
                           (coe
                              d_inferElabV_6570 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Internal.Typing.Scope.du_extendNamedCtx_150
                                 (coe v1) (coe v2) (coe v14))
                              (coe v3))
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v14 v15 v16
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C_μ_28 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C_ν_30 v14 v15
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C_Int_32
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Type.C_Float_34
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_100
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_100 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-auxL
d_inferElabV'45'RDestruct'45'auxL_6684 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
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
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RDestruct'45'auxL_6684 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7
                                       v8 v9 v10 v11 ~v12 v13 v14
  = du_inferElabV'45'RDestruct'45'auxL_6684
      v0 v1 v5 v6 v7 v8 v9 v10 v11 v13 v14
du_inferElabV'45'RDestruct'45'auxL_6684 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RDestruct'45'auxL_6684 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10
  = case coe v10 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
        -> case coe v11 of
             C_success_98 v13 v14 v15 v16 v17
               -> case coe v14 of
                    MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v19 v20
                      -> coe
                           du_inferElabV'45'RDestruct'45'auxR_4554 (coe v0) (coe v4) (coe v5)
                           (coe v6) (coe v7) (coe v8) (coe v9) (coe v13) (coe v19) (coe v20)
                           (coe v15) (coe v16) (coe v12)
                           (coe
                              d_inferElabV_6570 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Internal.Typing.Scope.du_extendNamedCtx_150
                                 (coe v1) (coe v2) (coe v5))
                              (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_100 v13
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RApp-other-aux
d_inferElabV'45'RApp'45'other'45'aux_6696 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  Maybe
    MAlonzo.Code.Once.Internal.Typing.Scope.T_PolyBuiltinApp_272 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RApp'45'other'45'aux_6696 v0 v1 v2 v3 v4 ~v5
  = du_inferElabV'45'RApp'45'other'45'aux_6696 v0 v1 v2 v3 v4
du_inferElabV'45'RApp'45'other'45'aux_6696 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  Maybe
    MAlonzo.Code.Once.Internal.Typing.Scope.T_PolyBuiltinApp_272 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RApp'45'other'45'aux_6696 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe
                      ("unreachable: ahv-other \8658 classifyAppHead nothing"
                       ::
                       Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> let v5 = d_inferElabV_6570 (coe v0) (coe v1) (coe v2) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_98 v8 v9 v10 v11 v12
                         -> case coe v8 of
                              MAlonzo.Code.Once.Spec.Type.C_var_16 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_100
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                           (coe v0) (coe v8)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Spec.Type.C_Unit_18
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_100
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                           (coe (0 :: Integer)) (coe v8)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Spec.Type.C_Void_20
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_100
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                           (coe (0 :: Integer)) (coe v8)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Spec.Type.C__'42'__22 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_100
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                           (coe v0) (coe v8)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Spec.Type.C__'43'__24 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_100
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                           (coe v0) (coe v8)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v13 v14 v15
                                -> case coe v14 of
                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v16 v17
                                       -> case coe v17 of
                                            MAlonzo.Code.Once.Spec.Grade.C_fin_42 v18
                                              -> case coe v18 of
                                                   MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                                     -> let v19
                                                              = coe
                                                                  du_checkElabV'45'wf_6590 (coe v0)
                                                                  (coe v1) (coe v3) (coe v13) in
                                                        coe
                                                          (case coe v19 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                               -> case coe v20 of
                                                                    C_success_126 v22 v23 v24 v25
                                                                      -> coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe
                                                                              C_success_98 (coe v15)
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                                                 v9
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                                                                                    v16 v22))
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Surface.Syntax.C_app_54
                                                                                 v9 v22 v13 v16 v10
                                                                                 v23)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                 (coe v11)
                                                                                 (coe v24))
                                                                              (coe v25))
                                                                           (coe
                                                                              MAlonzo.Code.Once.Internal.Typing.C_t'45'app_398
                                                                              v13 v16 v9 v22 v7 v21)
                                                                    C_failure_128 v22
                                                                      -> coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe
                                                                              C_failure_100
                                                                              (coe v22))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                   MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                                     -> case coe v16 of
                                                          MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                                            -> coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe
                                                                    C_failure_100
                                                                    (coe
                                                                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                                                       (coe v0) (coe v8)))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                          MAlonzo.Code.Once.Spec.Grade.C_One_10
                                                            -> coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe
                                                                    C_failure_100
                                                                    (coe
                                                                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                                                       (coe v0) (coe v8)))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                          MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                                            -> let v19
                                                                     = coe
                                                                         du_checkElabV'45'wf_6590
                                                                         (coe v0) (coe v1) (coe v3)
                                                                         (coe v13) in
                                                               coe
                                                                 (case coe v19 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                      -> case coe v20 of
                                                                           C_success_126 v22 v23 v24 v25
                                                                             -> coe
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                  (coe
                                                                                     C_success_98
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                                                                        (coe v14)
                                                                                        (coe v15))
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                                                        v9
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                                                                                           v16 v22))
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Surface.Syntax.C_effApp_72
                                                                                        v9 v22 v13
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Spec.Grade.C_eg'45'act_70)
                                                                                        v10 v23)
                                                                                     (coe
                                                                                        MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                        (coe v11)
                                                                                        (coe v24))
                                                                                     (coe v25))
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Internal.Typing.C_t'45'effApp_418
                                                                                     v13 v9 v22
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Spec.Grade.C_eg'45'act_70)
                                                                                     v7 v21)
                                                                           C_failure_128 v22
                                                                             -> coe
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                  (coe
                                                                                     C_failure_100
                                                                                     (coe v22))
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                              -> case coe v16 of
                                                   MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             C_failure_100
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                                                (coe v0) (coe v8)))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   MAlonzo.Code.Once.Spec.Grade.C_One_10
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             C_failure_100
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                                                (coe v0) (coe v8)))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                                     -> let v18
                                                              = coe
                                                                  du_checkElabV'45'wf_6590 (coe v0)
                                                                  (coe v1) (coe v3) (coe v13) in
                                                        coe
                                                          (case coe v18 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                               -> case coe v19 of
                                                                    C_success_126 v21 v22 v23 v24
                                                                      -> coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe
                                                                              C_success_98
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                                                                 (coe v14)
                                                                                 (coe v15))
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                                                 v9
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                                                                                    v16 v21))
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Surface.Syntax.C_effApp_72
                                                                                 v9 v21 v13
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Spec.Grade.C_eg'45'eff_72)
                                                                                 v10 v22)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                 (coe v11)
                                                                                 (coe v23))
                                                                              (coe v24))
                                                                           (coe
                                                                              MAlonzo.Code.Once.Internal.Typing.C_t'45'effApp_418
                                                                              v13 v9 v21
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Spec.Grade.C_eg'45'eff_72)
                                                                              v7 v20)
                                                                    C_failure_128 v21
                                                                      -> coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe
                                                                              C_failure_100
                                                                              (coe v21))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Spec.Type.C_μ_28 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_100
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                           (coe v0) (coe v8)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Spec.Type.C_ν_30 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_100
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                           (coe v0) (coe v8)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Spec.Type.C_Int_32
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_100
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                           (coe (0 :: Integer)) (coe v8)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Spec.Type.C_Float_34
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_100
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                           (coe (0 :: Integer)) (coe v8)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       C_failure_100 v8
                         -> coe
                              du_inferSpine_6732 (coe v0) (coe v1) (coe v2)
                              (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v3))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RApp-dispatch
d_inferElabV'45'RApp'45'dispatch_6708 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_AppHeadView_306 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RApp'45'dispatch_6708 v0 v1 v2 v3 v4 ~v5
  = du_inferElabV'45'RApp'45'dispatch_6708 v0 v1 v2 v3 v4
du_inferElabV'45'RApp'45'dispatch_6708 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_AppHeadView_306 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RApp'45'dispatch_6708 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'id_308
        -> let v5 = d_inferElabV_6570 (coe v0) (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_98 v8 v9 v10 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_98 (coe v8)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                    (MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                       (coe
                                          MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132
                                          (coe v1)))
                                    (coe
                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v9))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v9 v8
                                    (coe MAlonzo.Code.Once.IR.C_id_20) v10)
                                 (coe addInt (coe (1 :: Integer)) (coe v11)) (coe v12))
                              (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'id'45'app_294 v9 v7)
                       C_failure_100 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'fst_310
        -> coe
             du_inferFstOn_2570 (coe v1)
             (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'snd_312
        -> coe
             du_inferSndOn_2650 (coe v1)
             (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'terminal_314
        -> let v5 = d_inferElabV_6570 (coe v0) (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_98 v8 v9 v10 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                    (MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                       (coe
                                          MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132
                                          (coe v1)))
                                    (coe
                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v9))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v9 v8
                                    (coe MAlonzo.Code.Once.IR.C_terminal_72) v10)
                                 (coe addInt (coe (1 :: Integer)) (coe v11)) (coe v12))
                              (coe
                                 MAlonzo.Code.Once.Internal.Typing.C_t'45'terminal'45'app_328 v8 v9
                                 v7)
                       C_failure_100 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'inl_316
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlInInferMode_28))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'inr_318
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrInInferMode_30))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'initial_320
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_InitialInInferMode_32))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'curry_322
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("curry" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'apply_324
        -> coe
             du_inferApplyOn_2904 (coe v0) (coe v1)
             (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'In_326
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("In" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'cata_328
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("cata" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'ana_330
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("ana" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'Out_332
        -> coe d_inferOut_6444 (coe v0) (coe v1) (coe v3)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'pair'45'applied_336
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("pair" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'compose'45'applied_340
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("compose" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'case'45'applied_344
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("case" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'other_348
        -> coe
             d_inferElabV'45'RApp'45'other_6600 (coe v0) (coe v1) (coe v2)
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RApp-dispatch
d_checkElabV'45'RApp'45'dispatch_6722 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_AppHeadView_306 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RApp'45'dispatch_6722 v0 v1 v2 v3 v4 v5 ~v6
  = du_checkElabV'45'RApp'45'dispatch_6722 v0 v1 v2 v3 v4 v5
du_checkElabV'45'RApp'45'dispatch_6722 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_AppHeadView_306 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RApp'45'dispatch_6722 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'id_308
        -> let v6 = d_inferElabV_6570 (coe v0) (coe v1) (coe v3) in
           coe
             (case coe v6 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                  -> case coe v7 of
                       C_success_98 v9 v10 v11 v12 v13
                         -> let v14
                                  = coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                      (coe
                                         C_success_98 (coe v9)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                            (MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132
                                                  (coe v1)))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v10
                                            v9 (coe MAlonzo.Code.Once.IR.C_id_20) v11)
                                         (coe addInt (coe (1 :: Integer)) (coe v12)) (coe v13))
                                      (coe
                                         MAlonzo.Code.Once.Internal.Typing.C_t'45'id'45'app_294 v10
                                         v8) in
                            coe (coe du_embedOrSubsume_734 (coe v0) (coe v4) (coe v14))
                       C_failure_100 v9
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_128 (coe v9))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'fst_310
        -> let v6
                 = coe
                     du_inferFstOn_2570 (coe v1)
                     (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v3)) in
           coe
             (case coe v6 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                  -> case coe v7 of
                       C_success_98 v9 v10 v11 v12 v13
                         -> coe du_embedOrSubsume_734 (coe v0) (coe v4) (coe v6)
                       C_failure_100 v9
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_128 (coe v9))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'snd_312
        -> let v6
                 = coe
                     du_inferSndOn_2650 (coe v1)
                     (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v3)) in
           coe
             (case coe v6 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                  -> case coe v7 of
                       C_success_98 v9 v10 v11 v12 v13
                         -> coe du_embedOrSubsume_734 (coe v0) (coe v4) (coe v6)
                       C_failure_100 v9
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_128 (coe v9))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'terminal_314
        -> let v6 = d_inferElabV_6570 (coe v0) (coe v1) (coe v3) in
           coe
             (case coe v6 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                  -> case coe v7 of
                       C_success_98 v9 v10 v11 v12 v13
                         -> let v14
                                  = coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                      (coe
                                         C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                            (MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132
                                                  (coe v1)))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v10
                                            v9 (coe MAlonzo.Code.Once.IR.C_terminal_72) v11)
                                         (coe addInt (coe (1 :: Integer)) (coe v12)) (coe v13))
                                      (coe
                                         MAlonzo.Code.Once.Internal.Typing.C_t'45'terminal'45'app_328
                                         v9 v10 v8) in
                            coe (coe du_embedOrSubsume_734 (coe v0) (coe v4) (coe v14))
                       C_failure_100 v9
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_128 (coe v9))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'inl_316
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_128
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_128
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_128
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_128
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v6 v7
               -> let v8
                        = coe
                            du_checkElabV'45'wf_6590 (coe v0) (coe v1) (coe v3) (coe v6) in
                  coe
                    (case coe v8 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                         -> case coe v9 of
                              C_success_126 v11 v12 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_success_126
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                           (MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                              (coe
                                                 MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132
                                                 (coe v1)))
                                           (coe
                                              MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v11))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v11
                                           v6 (coe MAlonzo.Code.Once.IR.C_inl_54) v12)
                                        (coe addInt (coe (1 :: Integer)) (coe v13)) (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Typing.C_t'45'inl'45'app'45'check_750
                                        v11 v10)
                              C_failure_128 v11
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v6 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_128
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_128
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_128
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_Int_32
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_128
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_128
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'inr_318
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_128
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_128
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_128
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_128
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v6 v7
               -> let v8
                        = coe
                            du_checkElabV'45'wf_6590 (coe v0) (coe v1) (coe v3) (coe v7) in
                  coe
                    (case coe v8 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                         -> case coe v9 of
                              C_success_126 v11 v12 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_success_126
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                           (MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                              (coe
                                                 MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132
                                                 (coe v1)))
                                           (coe
                                              MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v11))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v11
                                           v7 (coe MAlonzo.Code.Once.IR.C_inr_60) v12)
                                        (coe addInt (coe (1 :: Integer)) (coe v13)) (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Typing.C_t'45'inr'45'app'45'check_762
                                        v11 v10)
                              C_failure_128 v11
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v6 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_128
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_128
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_128
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_Int_32
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_128
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_128
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'initial_320
        -> let v6
                 = coe
                     du_checkElabV'45'wf_6590 (coe v0) (coe v1) (coe v3)
                     (coe MAlonzo.Code.Once.Spec.Type.C_Void_20) in
           coe
             (case coe v6 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                  -> case coe v7 of
                       C_success_126 v9 v10 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_126
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                    (MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                       (coe
                                          MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132
                                          (coe v1)))
                                    (coe
                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v9))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v9
                                    (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
                                    (coe MAlonzo.Code.Once.IR.C_initial_76) v10)
                                 (coe addInt (coe (1 :: Integer)) (coe v11)) (coe v12))
                              (coe
                                 MAlonzo.Code.Once.Internal.Typing.C_t'45'initial'45'app'45'check_772
                                 v9 v8)
                       C_failure_128 v9
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'curry_322
        -> coe d_checkCurry_6426 (coe v0) (coe v1) (coe v3) (coe v4)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'apply_324
        -> let v6
                 = coe
                     du_inferApplyOn_2904 (coe v0) (coe v1)
                     (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v3)) in
           coe
             (case coe v6 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                  -> case coe v7 of
                       C_success_98 v9 v10 v11 v12 v13
                         -> coe du_embedOrSubsume_734 (coe v0) (coe v4) (coe v6)
                       C_failure_100 v9
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_128 (coe v9))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'In_326
        -> coe d_checkIn_6454 (coe v0) (coe v1) (coe v3) (coe v4)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'cata_328
        -> coe d_checkCata_6486 (coe v0) (coe v1) (coe v3) (coe v4)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'ana_330
        -> coe d_checkAna_6522 (coe v0) (coe v1) (coe v3) (coe v4)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'Out_332
        -> let v6
                 = coe
                     du_inferOutOn_2490 (coe v0) (coe v1)
                     (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v3)) in
           coe
             (case coe v6 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                  -> case coe v7 of
                       C_success_98 v9 v10 v11 v12 v13
                         -> coe du_embedOrSubsume_734 (coe v0) (coe v4) (coe v6)
                       C_failure_100 v9
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_128 (coe v9))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'pair'45'applied_336
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v7 v8
               -> coe
                    d_checkPair_6266 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76
                       (coe
                          MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74
                          (coe
                             MAlonzo.Code.Once.Spec.Name.C_canonical_12
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe ("Generators" :: Data.Text.Text))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe ("pair" :: Data.Text.Text))
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                       (coe v8))
                    (coe v3) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'compose'45'applied_340
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v7 v8
               -> coe
                    d_checkCompose_6346 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76
                       (coe
                          MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74
                          (coe
                             MAlonzo.Code.Once.Spec.Name.C_canonical_12
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe ("Generators" :: Data.Text.Text))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe ("compose" :: Data.Text.Text))
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                       (coe v8))
                    (coe v3) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'case'45'applied_344
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v7 v8
               -> coe
                    d_checkCase_6304 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76
                       (coe
                          MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74
                          (coe
                             MAlonzo.Code.Once.Spec.Name.C_canonical_12
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe ("Generators" :: Data.Text.Text))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe ("case" :: Data.Text.Text))
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                       (coe v8))
                    (coe v3) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'other_348
        -> let v7
                 = coe
                     du_inferElabV'45'RApp'45'dispatch_6708 (coe v0) (coe v1) (coe v2)
                     (coe v3)
                     (coe
                        MAlonzo.Code.Once.Internal.Typing.Scope.d_classifyAppHeadView_352
                        (coe v2)) in
           coe
             (case coe v7 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                  -> case coe v8 of
                       C_success_98 v10 v11 v12 v13 v14
                         -> coe du_embedOrSubsume_734 (coe v0) (coe v4) (coe v7)
                       C_failure_100 v10
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_128 (coe v10))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferSpine
d_inferSpine_6732 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferSpine_6732 v0 v1 v2 ~v3 ~v4 v5
  = du_inferSpine_6732 v0 v1 v2 v5
du_inferSpine_6732 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferSpine_6732 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v4 of
             C_success_98 v6 v7 v8 v9 v10
               -> let v11
                        = d_elabGivenV_6370
                            (coe v0) (coe v1) (coe v2) (coe v6)
                            (coe
                               MAlonzo.Code.Once.Spec.Grade.C_fin_42
                               (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)) in
                  coe
                    (case coe v11 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                         -> case coe v12 of
                              C_success_280 v14 v15 v16 v17 v18
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_success_98 (coe v14)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44 v15
                                           (coe
                                              MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v7))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_app_54 v15 v7 v6
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v16 v8)
                                        (coe
                                           addInt (coe (1 :: Integer))
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v17)
                                              (coe v9)))
                                        (coe v18))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Typing.C_t'45'app'45'spine_434 v6
                                        v15 v7 v5 v13)
                              C_failure_282 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe C_failure_100 (coe v14))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             C_failure_100 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RInt-aux
d_checkElabV'45'RInt'45'aux_6742 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RInt'45'aux_6742 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                 (coe
                    MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                    (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                 (coe MAlonzo.Code.Once.Surface.Syntax.C_int_194 v2)
                 (coe (0 :: Integer)) (coe (0 :: Integer)))
              (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'int_38) in
    coe (coe du_embedOrSubsume_734 (coe v0) (coe v3) (coe v4))
-- Once.TypeCheck.Elaborate.checkElabV-RPair-aux
d_checkElabV'45'RPair'45'aux_6754 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_RPairTarget_32 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RPair'45'aux_6754 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_rpt'45'prod_40
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v8 v9
               -> coe
                    d_checkPairLit_6292 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8)
                    (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_rpt'45'vlift_50
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v10 v11 v12
               -> case coe v11 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_128
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v10)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v14))
                                    (coe v12))
                                 (coe v12)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_rpt'45'other_54
        -> let v7
                 = coe
                     du_inferElabV'45'RPair'45'aux_2936
                     (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v2))
                     (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v3)) in
           coe (coe du_embedOrSubsume_734 (coe v0) (coe v4) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElab
d_inferElab_10274 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_InferElabResult_82
d_inferElab_10274 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.Elaborate.checkElab
d_checkElab_10290 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkElab_10290 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_checkElabV_6580 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.TypeCheck.Elaborate.checkApply
d_checkApply_10310 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkApply_10310 v0 v1 v2 v3
  = let v4 = d_inferElabV_6570 (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                C_success_98 v7 v8 v9 v10 v11
                  -> case coe v7 of
                       MAlonzo.Code.Once.Spec.Type.C_var_16 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_128
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Spec.Type.C_Unit_18
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_128
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Spec.Type.C_Void_20
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_128
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Spec.Type.C__'42'__22 v12 v13
                         -> case coe v12 of
                              MAlonzo.Code.Once.Spec.Type.C_var_16 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_128
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Spec.Type.C_Unit_18
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_128
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Spec.Type.C_Void_20
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_128
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Spec.Type.C__'42'__22 v14 v15
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_128
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Spec.Type.C__'43'__24 v14 v15
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_128
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v14 v15 v16
                                -> case coe v15 of
                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v17 v18
                                       -> case coe v17 of
                                            MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                              -> case coe v18 of
                                                   MAlonzo.Code.Once.Spec.Grade.C_fin_42 v19
                                                     -> coe
                                                          seq (coe v19)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                C_failure_128
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                   (coe
                                                                      ("apply" :: Data.Text.Text))))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                   MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             C_failure_128
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                (coe ("apply" :: Data.Text.Text))))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            MAlonzo.Code.Once.Spec.Grade.C_One_10
                                              -> case coe v18 of
                                                   MAlonzo.Code.Once.Spec.Grade.C_fin_42 v19
                                                     -> coe
                                                          seq (coe v19)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                C_failure_128
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                   (coe
                                                                      ("apply" :: Data.Text.Text))))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                   MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             C_failure_128
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                (coe ("apply" :: Data.Text.Text))))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                              -> case coe v18 of
                                                   MAlonzo.Code.Once.Spec.Grade.C_fin_42 v19
                                                     -> case coe v19 of
                                                          MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                                            -> let v20
                                                                     = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__230
                                                                         (coe v0) (coe v14)
                                                                         (coe v13) in
                                                               coe
                                                                 (let v21
                                                                        = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__230
                                                                            (coe v0) (coe v3)
                                                                            (coe v16) in
                                                                  coe
                                                                    (case coe v20 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                                         -> if coe v22
                                                                              then coe
                                                                                     seq (coe v23)
                                                                                     (case coe
                                                                                             v21 of
                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                                                          -> if coe
                                                                                                  v24
                                                                                               then coe
                                                                                                      seq
                                                                                                      (coe
                                                                                                         v25)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                         (coe
                                                                                                            C_success_126
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44
                                                                                                               (MAlonzo.Code.Once.Internal.Context.d_zeroUsage_36
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132
                                                                                                                     (coe
                                                                                                                        v1)))
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                                                                                                                  v17
                                                                                                                  v8))
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438
                                                                                                               v8
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Once.Spec.Type.C__'42'__22
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
                                                                                                            (coe
                                                                                                               v11))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Internal.Typing.C_t'45'apply'45'check_738
                                                                                                            v14
                                                                                                            v8
                                                                                                            v6))
                                                                                               else coe
                                                                                                      seq
                                                                                                      (coe
                                                                                                         v25)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                         (coe
                                                                                                            C_failure_128
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                                                                               (coe
                                                                                                                  v0)
                                                                                                               (coe
                                                                                                                  v3)
                                                                                                               (coe
                                                                                                                  v16)))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                                                              else coe
                                                                                     seq (coe v23)
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                        (coe
                                                                                           C_failure_128
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
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
                                                                    C_failure_128
                                                                    (coe
                                                                       MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
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
                                                             C_failure_128
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                (coe ("apply" :: Data.Text.Text))))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Spec.Type.C_μ_28 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_128
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Spec.Type.C_ν_30 v14 v15
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_128
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Spec.Type.C_Int_32
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_128
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Spec.Type.C_Float_34
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_128
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Spec.Type.C__'43'__24 v12 v13
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_128
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v12 v13 v14
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_128
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Spec.Type.C_μ_28 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_128
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Spec.Type.C_ν_30 v12 v13
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_128
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Spec.Type.C_Int_32
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_128
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Spec.Type.C_Float_34
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_128
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                C_failure_100 v7
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe C_failure_128 (coe v7))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.inferElab-RApp-other
d_inferElab'45'RApp'45'other_10578 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_InferElabResult_82
d_inferElab'45'RApp'45'other_10578 v0 v1 v2 v3
  = let v4
          = coe
              du_asFun_1206 (coe v0)
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe d_inferElabV_6570 (coe v0) (coe v1) (coe v2))) in
    coe
      (case coe v4 of
         C_isFun_1184 v5 v6 v7 v8 v9 v10 v11
           -> let v12
                    = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe
                           du_checkElabV'45'wf_6590 (coe v0) (coe v1) (coe v3) (coe v5)) in
              coe
                (case coe v12 of
                   C_success_126 v13 v14 v15 v16
                     -> coe
                          C_success_98 (coe v7)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44 v8
                             (coe MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48 v6 v13))
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_app_54 v8 v13 v5 v6 v9 v14)
                          (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v10) (coe v15))
                          (coe v16)
                   C_failure_128 v13 -> coe C_failure_100 (coe v13)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         C_isEff_1196 v5 v6 v7 v8 v9 v10 v11 v12
           -> let v13
                    = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe
                           du_checkElabV'45'wf_6590 (coe v0) (coe v1) (coe v3) (coe v7)) in
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
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__44 v9
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__48
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v14))
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_effApp_72 v9 v14 v7 v6 v10 v15)
                          (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v11) (coe v16))
                          (coe v17)
                   C_failure_128 v14 -> coe C_failure_100 (coe v14)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         C_notFun_1198 v5 -> coe C_failure_100 (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
