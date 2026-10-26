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

module MAlonzo.Code.Once.TypeCheck.Link where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Scope

-- Once.TypeCheck.Link.resolveExprWF
d_resolveExprWF_18 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_resolveExprWF_18 v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 v8 v9 v10
  = du_resolveExprWF_18 v0 v4 v5 v7 v8 v9 v10
du_resolveExprWF_18 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_resolveExprWF_18 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_20 v9
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_var_20 v9
      MAlonzo.Code.Once.Surface.Syntax.C_lam_38 v10 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_38 v10
                    (coe
                       du_resolveExprWF_18 (coe v0) (coe v19) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_54 v9 v10 v11 v13 v14 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_54 v9 v10 v11 v13
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe
                   MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v11)
                   (coe
                      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v13)
                      (coe
                         MAlonzo.Code.Once.Spec.Grade.C_fin_42
                         (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                   (coe v1))
                (coe v2) (coe v3) (coe v4) (coe v5) (coe v14))
             (coe
                du_resolveExprWF_18 (coe v0) (coe v11) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v15))
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_72 v9 v10 v11 v14 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v20 v21
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_effApp_72 v9 v10 v11 v14
                           (coe
                              du_resolveExprWF_18 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v11)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v21))
                                 (coe v19))
                              (coe v2) (coe v3) (coe v4) (coe v5) (coe v15))
                           (coe
                              du_resolveExprWF_18 (coe v0) (coe v11) (coe v2) (coe v3) (coe v4)
                              (coe v5) (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_86 v9 v10 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_86 v9 v10
                    (coe
                       du_resolveExprWF_18 (coe v0) (coe v15) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v13))
                    (coe
                       du_resolveExprWF_18 (coe v0) (coe v16) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_98 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_98 v11
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v1) (coe v11))
                (coe v2) (coe v3) (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_110 v10 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_110 v10
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v10) (coe v1))
                (coe v2) (coe v3) (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_122 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_122
                    (coe
                       du_resolveExprWF_18 (coe v0) (coe v13) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_134 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_134
                    (coe
                       du_resolveExprWF_18 (coe v0) (coe v14) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_156 v9 v10 v11 v12 v13 v14 v15 v17 v18 v19
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_156 v9 v10 v11 v12 v13
             v14 v15
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v14) (coe v15))
                (coe v2) (coe v3) (coe v4) (coe v5) (coe v17))
             (coe
                du_resolveExprWF_18 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v18))
             (coe
                du_resolveExprWF_18 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v19))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_162
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_162
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_172 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_172
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Void_20) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_188 v9 v10 v11 v12 v14 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_188 v9 v10 v11 v12
             (coe
                du_resolveExprWF_18 (coe v0) (coe v12) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v14))
             (coe
                du_resolveExprWF_18 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v15))
      MAlonzo.Code.Once.Surface.Syntax.C_int_194 v9
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_int_194 v9
      MAlonzo.Code.Once.Surface.Syntax.C_float_202 v9
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_float_202 v9
      MAlonzo.Code.Once.Surface.Syntax.C_add_212 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_add_212 v9 v10
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_222 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_sub_222 v9 v10
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_232 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mul_232 v9 v10
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_fadd_242 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fadd_242 v9 v10
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_fsub_252 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fsub_252 v9 v10
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_fmul_262 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fmul_262 v9 v10
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_fdiv_272 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fdiv_272 v9 v10
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_i2f_280 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_i2f_280
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_div_290 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_div_290 v9 v10
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_300 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mod''_300 v9 v10
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_308 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_neg_308
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_318 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lt_318 v9 v10
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_le_328 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_le_328 v9 v10
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_338 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_gt_338 v9 v10
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_348 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ge_348 v9 v10
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_358 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_eq_358 v9 v10
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_368 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ne_368 v9 v10
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_18 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v10 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v10 v12
             (coe
                du_resolveExprWF_18 (coe v0) (coe v10) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_388 v9 v10 v11
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_388 v9 v10 v11
      MAlonzo.Code.Once.Surface.Syntax.C_closure_396 v10
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_closure_396 v10
      MAlonzo.Code.Once.Surface.Syntax.C_poly_406 v9
        -> coe
             du_resolvePolyCase_34 (coe v0) (coe v3) (coe v4) (coe v5) (coe v9)
             (coe v1)
             (coe
                MAlonzo.Code.Once.TypeCheck.Scope.d_lookupPolyPrefix_74 (coe v2)
                (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_closed_414 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_closed_414
             (coe
                du_resolveExprWF_18 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426 v12
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426 v12
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v9 v10 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v9 v10 v12
             (coe
                du_resolveExprWF_18 (coe v0) (coe v10) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_comp''_456 v9 v10 v12 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v20 v21
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_comp''_456 v9 v10 v12
                           (coe
                              du_resolveExprWF_18 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v12)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v21))
                                 (coe v19))
                              (coe v2) (coe v3) (coe v4) (coe v5) (coe v15))
                           (coe
                              du_resolveExprWF_18 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v17)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v21))
                                 (coe v12))
                              (coe v2) (coe v3) (coe v4) (coe v5) (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_copair''_474 v9 v10 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> case coe v17 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v20 v21
                      -> case coe v18 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v22 v23
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_copair''_474 v9 v10
                                  (coe
                                     du_resolveExprWF_18 (coe v0)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v20)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v23))
                                        (coe v19))
                                     (coe v2) (coe v3) (coe v4) (coe v5) (coe v15))
                                  (coe
                                     du_resolveExprWF_18 (coe v0)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v21)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v23))
                                        (coe v19))
                                     (coe v2) (coe v3) (coe v4) (coe v5) (coe v16))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fork''_492 v9 v10 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v20 v21
                      -> case coe v19 of
                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 v22 v23
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_fork''_492 v9 v10
                                  (coe
                                     du_resolveExprWF_18 (coe v0)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v17)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v21))
                                        (coe v22))
                                     (coe v2) (coe v3) (coe v4) (coe v5) (coe v15))
                                  (coe
                                     du_resolveExprWF_18 (coe v0)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v17)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v21))
                                        (coe v23))
                                     (coe v2) (coe v3) (coe v4) (coe v5) (coe v16))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_curry''_510 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v16 v17 v18
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v19 v20 v21
                      -> case coe v20 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v22 v23
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_curry''_510
                                  (coe
                                     du_resolveExprWF_18 (coe v0)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v16)
                                           (coe v19))
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v23))
                                        (coe v21))
                                     (coe v2) (coe v3) (coe v4) (coe v5) (coe v15))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_cata_526 v9 v11 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v16 v17 v18
               -> case coe v16 of
                    MAlonzo.Code.Once.Spec.Type.C_μ_28 v19
                      -> case coe v17 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v20 v21
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_cata_526 v9 v11 v14
                                  (coe
                                     du_resolveExprWF_18 (coe v0)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50
                                           (coe v19) (coe v18))
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v21))
                                        (coe v18))
                                     (coe v2) (coe v3) (coe v4) (coe v5) (coe v15))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_544 v9 v11 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> case coe v19 of
                    MAlonzo.Code.Once.Spec.Type.C_ν_30 v20 v21
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_ana_544 v9 v11 v15
                           (coe
                              du_resolveExprWF_18 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v17)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v21)))
                                 (coe
                                    MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v20)
                                    (coe v17)))
                              (coe v2) (coe v3) (coe v4) (coe v5) (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_loop_556 v9 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_loop_556 v9
                    (coe
                       du_resolveExprWF_18 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v13)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
                          (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v15) (coe v13)))
                       (coe v2) (coe v3) (coe v4) (coe v5) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Link.resolvePolyCase
d_resolvePolyCase_34 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_resolvePolyCase_34 v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10 ~v11
  = du_resolvePolyCase_34 v0 v5 v6 v7 v8 v9 v10
du_resolvePolyCase_34 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_resolvePolyCase_34 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> case coe v9 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> coe
                           du_applySplice_56 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                           (coe v5) (coe v11)
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_6032 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.du_ctxAt_354
                                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_baseKinds_364 (coe v0))
                                 (coe v1 v4) (coe v11))
                              (coe v10) (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_406 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Link.applySplice
d_applySplice_56 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_110 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_applySplice_56 v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 ~v10 ~v11 v12
                 ~v13 v14
  = du_applySplice_56 v0 v5 v6 v7 v8 v9 v12 v14
du_applySplice_56 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_110 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_applySplice_56 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_126 v8 v9 v10 v11
        -> coe
             seq (coe v8)
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_closed_414
                (coe
                   du_resolveExprWF_18 (coe v0) (coe v5) (coe v6) (coe v1) (coe v2)
                   (coe v3) (coe v9)))
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_128 v8
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_406 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Link.resolveExpr
d_resolveExpr_718 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_resolveExpr_718 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_resolveExpr_718 v0 v4 v5 v6 v7 v8 v9
du_resolveExpr_718 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_resolveExpr_718 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_resolveExprWF_18 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6)
