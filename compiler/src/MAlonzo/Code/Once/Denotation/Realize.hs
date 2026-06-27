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

module MAlonzo.Code.Once.Denotation.Realize where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Arith.SigOp.Builders
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.Denotation.Realize.realize
d_realize_14 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184
d_realize_14 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_540 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v11 v12 v13
               -> case coe v12 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                           (d_realize'45'morph_60
                              (coe v0) (coe v1) (coe v11) (coe v13) (coe v15) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_550 v9
        -> coe
             d_realize'45'infer_24 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_568 v11 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v17 v18 v19
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_lam_208 v11
                           (d_realize_14
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_200
                                 (coe
                                    addInt (coe (1 :: Integer))
                                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0)))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                                    (coe v15) (coe v17))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190 (coe v0))
                                    (coe v17))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                    (coe v0))
                                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
                                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_196 (coe v0))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_sigEffects_198 (coe v0)))
                              (coe v16) (coe v19)
                              (coe MAlonzo.Code.Once.Surface.Syntax.C__'8759'__66 v11 v3)
                              (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_578 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                    (coe du_realize'45'global_34 (coe v1) (coe v12) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_594 v10 v11 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_pair_252 v10 v11
                           (d_realize_14 (coe v0) (coe v14) (coe v16) (coe v10) (coe v12))
                           (d_realize_14 (coe v0) (coe v15) (coe v17) (coe v11) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_606 v8 v9 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_546 v9
                           (MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v14) (coe v2))
                           (coe
                              MAlonzo.Code.Once.IR.C_In_108 v8
                              (coe MAlonzo.Code.Once.IR.C_Heap_8))
                           (d_realize_14
                              (coe v0) (coe v13)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v14) (coe v2))
                              (coe v9) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_618 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_546 v9
                    (coe
                       MAlonzo.Code.Once.Type.C__'42'__126
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v7)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v2))
                       (coe v7))
                    (coe MAlonzo.Code.Once.IR.C_apply_96)
                    (d_realize'45'infer_24
                       (coe v0) (coe v12)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__126
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v7)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v2))
                          (coe v7))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_630 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_546 v9 v13
                           (coe
                              MAlonzo.Code.Once.IR.C_inl_56 (coe MAlonzo.Code.Once.IR.C_Heap_8))
                           (d_realize_14 (coe v0) (coe v12) (coe v13) (coe v9) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_642 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_546 v9 v14
                           (coe
                              MAlonzo.Code.Once.IR.C_inr_62 (coe MAlonzo.Code.Once.IR.C_Heap_8))
                           (d_realize_14 (coe v0) (coe v12) (coe v14) (coe v9) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_652 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_546 v8
                    (coe MAlonzo.Code.Once.Type.C_Void_124)
                    (coe MAlonzo.Code.Once.IR.C_initial_78)
                    (d_realize_14
                       (coe v0) (coe v11) (coe MAlonzo.Code.Once.Type.C_Void_124) (coe v8)
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arr'45'app'45'check_664 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_arr''_496
                           (d_realize_14
                              (coe v0) (coe v12)
                              (coe MAlonzo.Code.Once.Type.d__'8658'__150 (coe v13) (coe v15))
                              (coe v3) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_680 v8 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_app_224 v10 v11 v8
                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                    (d_realize_14
                       (coe v0) (coe v15)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v8)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v2))
                       (coe v10) (coe v14))
                    (d_realize'45'infer_24
                       (coe v0) (coe v16) (coe v8) (coe v11) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_692 v8 v9 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v16
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_522 v16
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Realize.realize-infer
d_realize'45'infer_24 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184
d_realize'45'infer_24 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v7
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_int_360 v7
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_36
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_56 v7
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_str_366 v7
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_40
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_328
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_44
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_328
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_56 v9
        -> coe v9
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_66
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504
                    (MAlonzo.Code.Once.CanonicalName.d_bare_12
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20 v11
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             ("." :: Data.Text.Text) v10)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_74
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v9
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504 v9
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_82
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504
                    (MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_92 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_58 v10 v11
               -> coe d_realize_14 (coe v0) (coe v10) (coe v2) (coe v3) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_108 v10 v11 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_pair_252 v10 v11
                           (d_realize'45'infer_24
                              (coe v0) (coe v14) (coe v16) (coe v10) (coe v12))
                           (d_realize'45'infer_24
                              (coe v0) (coe v15) (coe v17) (coe v11) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_116 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_62 v10
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_neg_424
                    (d_realize'45'infer_24
                       (coe v0) (coe v10) (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3)
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_136 v9 v11 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v16 v17 v18
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_let''_354 v12 v13 v11 v9
                    (d_realize'45'infer_24
                       (coe v0) (coe v17) (coe v9) (coe v12) (coe v14))
                    (d_realize'45'infer_24
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_200
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                             (coe v16) (coe v9))
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190 (coe v0))
                             (coe v9))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_196 (coe v0))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_sigEffects_198 (coe v0)))
                       (coe v18) (coe v2)
                       (coe MAlonzo.Code.Once.Surface.Syntax.C__'8759'__66 v11 v13)
                       (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_166 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v22 v23 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_case''_322 v16 v17 v18 v14 v15
                    v11 v12
                    (d_realize'45'infer_24
                       (coe v0) (coe v22)
                       (coe MAlonzo.Code.Once.Type.C__'43'__128 (coe v11) (coe v12))
                       (coe v16) (coe v19))
                    (d_realize'45'infer_24
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_200
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                             (coe v23) (coe v11))
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190 (coe v0))
                             (coe v11))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_196 (coe v0))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_sigEffects_198 (coe v0)))
                       (coe v24) (coe v2)
                       (coe MAlonzo.Code.Once.Surface.Syntax.C__'8759'__66 v14 v17)
                       (coe v20))
                    (d_realize'45'infer_24
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_200
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                             (coe v25) (coe v12))
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190 (coe v0))
                             (coe v12))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_196 (coe v0))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_sigEffects_198 (coe v0)))
                       (coe v26) (coe v2)
                       (coe MAlonzo.Code.Once.Surface.Syntax.C__'8759'__66 v15 v18)
                       (coe v21))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_180 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_60 v14 v15 v16
               -> case coe v14 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_add_376 v9 v10
                           (d_realize'45'infer_24
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_24
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_sub_386 v9 v10
                           (d_realize'45'infer_24
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_24
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_mul_396 v9 v10
                           (d_realize'45'infer_24
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_24
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_div_406 v9 v10
                           (d_realize'45'infer_24
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_24
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_mod''_416 v9 v10
                           (d_realize'45'infer_24
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_24
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10)
                              (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_194 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_60 v14 v15 v16
               -> case coe v14 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_lt_434 v9 v10
                           (d_realize'45'infer_24
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_24
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_le_444 v9 v10
                           (d_realize'45'infer_24
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_24
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_gt_454 v9 v10
                           (d_realize'45'infer_24
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_24
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_ge_464 v9 v10
                           (d_realize'45'infer_24
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_24
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_eq_474 v9 v10
                           (d_realize'45'infer_24
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_24
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_ne_484 v9 v10
                           (d_realize'45'infer_24
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_24
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10)
                              (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_204 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_546 v8 v2
                    (coe MAlonzo.Code.Once.IR.C_id_22)
                    (d_realize'45'infer_24
                       (coe v0) (coe v11) (coe v2) (coe v8) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_216 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_546 v9
                    (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v2) (coe v8))
                    (coe MAlonzo.Code.Once.IR.C_fst_44)
                    (d_realize'45'infer_24
                       (coe v0) (coe v12)
                       (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v2) (coe v8))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_228 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_546 v9
                    (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v7) (coe v2))
                    (coe MAlonzo.Code.Once.IR.C_snd_50)
                    (d_realize'45'infer_24
                       (coe v0) (coe v12)
                       (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v7) (coe v2))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_238 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_546 v8 v7
                    (coe MAlonzo.Code.Once.IR.C_terminal_74)
                    (d_realize'45'infer_24
                       (coe v0) (coe v11) (coe v7) (coe v8) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arr'45'app'45'infer_250 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_arr''_496
                           (d_realize'45'infer_24
                              (coe v0) (coe v12)
                              (coe MAlonzo.Code.Once.Type.d__'8658'__150 (coe v13) (coe v15))
                              (coe v3) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_262 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_546 v9
                    (coe
                       MAlonzo.Code.Once.Type.C__'42'__126
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v7)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v2))
                       (coe v7))
                    (coe MAlonzo.Code.Once.IR.C_apply_96)
                    (d_realize'45'infer_24
                       (coe v0) (coe v12)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__126
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v7)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v2))
                          (coe v7))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_280 v8 v10 v11 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_app_224 v11 v12 v8 v10
                    (d_realize'45'infer_24
                       (coe v0) (coe v16)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v8)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v2))
                       (coe v11) (coe v14))
                    (d_realize_14 (coe v0) (coe v17) (coe v8) (coe v12) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_296 v8 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v17 v18 v19
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_effApp_238 v10 v11 v8
                           (d_realize'45'infer_24
                              (coe v0) (coe v15)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v8)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe MAlonzo.Code.Once.Type.C_eff_36))
                                 (coe v19))
                              (coe v10) (coe v13))
                           (d_realize_14 (coe v0) (coe v16) (coe v8) (coe v11) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Realize.realize-global
d_realize'45'global_34 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_realize'45'global_34 ~v0 v1 v2 ~v3 v4
  = du_realize'45'global_34 v1 v2 v4
du_realize'45'global_34 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_realize'45'global_34 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_302
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v5
               -> coe MAlonzo.Code.Once.Surface.Elaborate.du_intLit_8 (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'terminal_306
        -> coe MAlonzo.Code.Once.IR.C_terminal_74
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_318 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v12 v13
                      -> coe
                           MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                           (coe du_realize'45'global_34 (coe v10) (coe v12) (coe v8))
                           (coe du_realize'45'global_34 (coe v11) (coe v13) (coe v9))
                           (coe MAlonzo.Code.Once.IR.C_Heap_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_328 v7
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v10 v11
                      -> coe
                           MAlonzo.Code.Once.IR.C__'8728'__30 v10
                           (coe
                              MAlonzo.Code.Once.IR.C_inl_56 (coe MAlonzo.Code.Once.IR.C_Heap_8))
                           (coe du_realize'45'global_34 (coe v9) (coe v10) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_338 v7
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v10 v11
                      -> coe
                           MAlonzo.Code.Once.IR.C__'8728'__30 v11
                           (coe
                              MAlonzo.Code.Once.IR.C_inr_62 (coe MAlonzo.Code.Once.IR.C_Heap_8))
                           (coe du_realize'45'global_34 (coe v9) (coe v11) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_348 v6 v8
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v11
                      -> coe
                           MAlonzo.Code.Once.IR.C__'8728'__30
                           (MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v11) (coe v1))
                           (coe
                              MAlonzo.Code.Once.IR.C_In_108 v6
                              (coe MAlonzo.Code.Once.IR.C_Heap_8))
                           (coe
                              du_realize'45'global_34 (coe v10)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v11) (coe v1))
                              (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Realize.realize-morph
d_realize'45'morph_60 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_realize'45'morph_60 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_356
        -> coe MAlonzo.Code.Once.IR.C_id_22
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_366
        -> coe MAlonzo.Code.Once.IR.C_fst_44
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_376
        -> coe MAlonzo.Code.Once.IR.C_snd_50
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_384
        -> coe MAlonzo.Code.Once.IR.C_terminal_74
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_392
        -> coe MAlonzo.Code.Once.IR.C_initial_78
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_402
        -> coe
             MAlonzo.Code.Once.IR.C_inl_56 (coe MAlonzo.Code.Once.IR.C_Heap_8)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_412
        -> coe
             MAlonzo.Code.Once.IR.C_inr_62 (coe MAlonzo.Code.Once.IR.C_Heap_8)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_428 v10 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
                      -> coe
                           MAlonzo.Code.Once.IR.C__'8728'__30 v10
                           (d_realize'45'morph_60
                              (coe v0) (coe v19) (coe v10) (coe v3) (coe v4) (coe v14))
                           (d_realize'45'morph_60
                              (coe v0) (coe v17) (coe v2) (coe v10) (coe v4) (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_444 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'43'__128 v19 v20
                             -> coe
                                  MAlonzo.Code.Once.IR.C_case_70
                                  (d_realize'45'morph_60
                                     (coe v0) (coe v18) (coe v19) (coe v3) (coe v4) (coe v13))
                                  (d_realize'45'morph_60
                                     (coe v0) (coe v16) (coe v20) (coe v3) (coe v4) (coe v14))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'pair_458 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
                      -> case coe v3 of
                           MAlonzo.Code.Once.Type.C__'42'__126 v18 v19
                             -> coe
                                  MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                                  (d_realize'45'morph_60
                                     (coe v0) (coe v17) (coe v2) (coe v18)
                                     (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v12))
                                  (d_realize'45'morph_60
                                     (coe v0) (coe v15) (coe v2) (coe v19)
                                     (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v13))
                                  (coe MAlonzo.Code.Once.IR.C_Heap_8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'curry_470 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v14 v15 v16
                      -> coe
                           MAlonzo.Code.Once.IR.C_curry_88
                           (d_realize'45'morph_60
                              (coe v0) (coe v13)
                              (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v2) (coe v14))
                              (coe v16) (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v11))
                           (coe MAlonzo.Code.Once.IR.C_Heap_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'cata_484 v11 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v16
                      -> coe
                           MAlonzo.Code.Once.IR.C_Cata_118 v11
                           (coe
                              MAlonzo.Code.Once.IR.C__'8728'__30
                              (coe
                                 MAlonzo.Code.Once.Type.C__'42'__126
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                    (coe
                                       MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v16)
                                       (coe v3))
                                    (coe
                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
                                    (coe v3))
                                 (coe
                                    MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v16)
                                    (coe v3)))
                              (coe MAlonzo.Code.Once.IR.C_apply_96)
                              (coe
                                 MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                                 (coe
                                    MAlonzo.Code.Once.IR.C__'8728'__30
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.du_'10214'_'10215''7580'_38
                                       (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_108
                                       (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                       (coe
                                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                          (coe
                                             MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v16)
                                             (coe v3))
                                          (coe
                                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                             (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
                                          (coe v3))
                                       (coe MAlonzo.Code.Once.IR.C_Heap_8)
                                       (coe
                                          d_realize_14
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_200
                                             (coe (0 :: Integer))
                                             (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                                             (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                             (coe (0 :: Integer))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                                (coe v0))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_polys_196
                                                (coe v0))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_emptySigEffects_12))
                                          (coe v15)
                                          (coe
                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                             (coe
                                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                (coe v16) (coe v3))
                                             (coe
                                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
                                             (coe v3))
                                          (coe
                                             MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_70
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_208
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                                      (coe v0))
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Classify.d_polys_196
                                                      (coe v0)))))
                                          (coe v13)))
                                    (coe MAlonzo.Code.Once.IR.C_terminal_74))
                                 (coe MAlonzo.Code.Once.IR.C_id_22)
                                 (coe MAlonzo.Code.Once.IR.C_Heap_8)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'arr_494 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    d_realize'45'morph_60 (coe v0) (coe v12) (coe v2) (coe v3)
                    (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_504 v10
        -> coe du_realize'45'global_34 (coe v1) (coe v3) (coe v10)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named_516
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v14
               -> coe
                    MAlonzo.Code.Once.IR.C_SigOp_166
                    (MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_198
                       (coe v2) (coe v3)
                       (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v14)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named'45'resolved_528
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v12
               -> coe
                    MAlonzo.Code.Once.IR.C_SigOp_166
                    (MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_198
                       (coe v2) (coe v3) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
