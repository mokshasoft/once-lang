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
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Arith.SigOp.Builders
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Surface.Thinning
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.Denotation.Realize.poly-usage-eq
d_poly'45'usage'45'eq_8 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_poly'45'usage'45'eq_8 = erased
-- Once.Denotation.Realize.realize
d_realize_20 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_realize_20 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v11 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_404
                    (coe du_realize'45'morph_88 (coe v1) (coe v11) (coe v13) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_642 v9
        -> coe
             d_realize'45'infer_30 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_660 v11 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v17 v18 v19
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_lam_32 v11
                           (d_realize_20
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_368
                                 (coe
                                    addInt (coe (1 :: Integer))
                                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                                    (coe v15) (coe v17))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0))
                                    (coe v17))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                    (coe v0))
                                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364 (coe v0))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_sigEffects_366 (coe v0)))
                              (coe v16) (coe v19)
                              (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v11 v3)
                              (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v11 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_404
                    (coe du_realize'45'global_40 (coe v1) (coe v13) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'closed'45'lift_684 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
               -> case coe v13 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                      -> case coe v16 of
                           MAlonzo.Code.Once.Type.C_pure_34
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_lam_32
                                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                                  (coe
                                     MAlonzo.Code.Once.Surface.Thinning.du_weaken_1010
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                        (coe v0))
                                     (coe v12) (coe v14) (coe MAlonzo.Code.Once.Type.C_Many_10)
                                     (coe
                                        d_realize'45'infer_30 (coe v0) (coe v1) (coe v14)
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                           (coe
                                              MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                              (coe v0)))
                                        (coe v11)))
                           MAlonzo.Code.Once.Type.C_eff_36
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_arr''_366
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_lam_32
                                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                                     (coe
                                        MAlonzo.Code.Once.Surface.Thinning.du_weaken_1010
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                           (coe v0))
                                        (coe v12) (coe v14) (coe MAlonzo.Code.Once.Type.C_Many_10)
                                        (coe
                                           d_realize'45'infer_30 (coe v0) (coe v1) (coe v14)
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                 (coe v0)))
                                           (coe v11))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_700 v10 v11 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_pair_76 v10 v11
                           (d_realize_20 (coe v0) (coe v14) (coe v16) (coe v10) (coe v12))
                           (d_realize_20 (coe v0) (coe v15) (coe v17) (coe v11) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_712 v8 v9 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_416 v9
                           (MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v14) (coe v2))
                           (coe
                              MAlonzo.Code.Once.IR.C_In_96
                              (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                 (coe v14) (coe v8))
                              (coe MAlonzo.Code.Once.IR.C_Heap_8))
                           (d_realize_20
                              (coe v0) (coe v13)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v14) (coe v2))
                              (coe v9) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_724 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_416 v9
                    (coe
                       MAlonzo.Code.Once.Type.C__'42'__122
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v7)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v2))
                       (coe v7))
                    (coe MAlonzo.Code.Once.IR.C_apply_92)
                    (d_realize'45'infer_30
                       (coe v0) (coe v12)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__122
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v7)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v2))
                          (coe v7))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_736 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_416 v9 v13
                           (coe
                              MAlonzo.Code.Once.IR.C_inl_56 (coe MAlonzo.Code.Once.IR.C_Heap_8))
                           (d_realize_20 (coe v0) (coe v12) (coe v13) (coe v9) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_748 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_416 v9 v14
                           (coe
                              MAlonzo.Code.Once.IR.C_inr_62 (coe MAlonzo.Code.Once.IR.C_Heap_8))
                           (d_realize_20 (coe v0) (coe v12) (coe v14) (coe v9) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_758 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_416 v8
                    (coe MAlonzo.Code.Once.Type.C_Void_120)
                    (coe MAlonzo.Code.Once.IR.C_initial_78)
                    (d_realize_20
                       (coe v0) (coe v11) (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v8)
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_770 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v11 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_arr''_366
                    (d_realize_20
                       (coe v0) (coe v1)
                       (coe MAlonzo.Code.Once.Type.d__'8658'__146 (coe v11) (coe v13))
                       (coe v3) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_786 v8 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_app_48 v10 v11 v8
                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                    (d_realize_20
                       (coe v0) (coe v15)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v8)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v2))
                       (coe v10) (coe v14))
                    (d_realize'45'infer_30
                       (coe v0) (coe v16) (coe v8) (coe v11) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_800 v8 v9 v10 v17
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_416
             (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
             (coe MAlonzo.Code.Once.Type.C_Unit_118)
             (coe
                MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_122
                (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8) (coe v2)
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe
                   d_realize_20
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_368
                      (coe (0 :: Integer))
                      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                      (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                      (coe (0 :: Integer))
                      (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                      (coe v10)
                      (coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptySigEffects_12))
                   (coe v9) (coe v2)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                      (coe
                         MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                         (coe
                            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                            (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                            (coe v10))))
                   (coe v17)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_152)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Realize.realize-infer
d_realize'45'infer_30 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_realize'45'infer_30 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v7
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_int_184 v7
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_42
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v10 v11 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_float_198
                    (MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28
                       (coe v10) (coe v11) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_48
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v7
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_str_190 v7
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_52
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_152
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_56
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_152
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_68 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.du_svar'8594'expr_450 (coe v9)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_78 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_sigOp_374
                    (MAlonzo.Code.Once.CanonicalName.d_bare_12
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20 v12
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             ("." :: Data.Text.Text) v11)))
                    v10
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_86 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v10
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_374 v10 v9
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_94 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_sigOp_374
                    (MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v12)) v11
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_110 v8 v9 v10 v11 v19
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_416
             (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
             (coe MAlonzo.Code.Once.Type.C_Unit_118)
             (coe
                MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_122
                (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8) (coe v2)
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe
                   d_realize_20
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_368
                      (coe (0 :: Integer))
                      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                      (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                      (coe (0 :: Integer))
                      (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                      (coe v10)
                      (coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptySigEffects_12))
                   (coe v9) (coe v2)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                      (coe
                         MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                         (coe
                            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                            (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                            (coe v10))))
                   (coe v19)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_152)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_120 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v10 v11
               -> coe d_realize_20 (coe v0) (coe v10) (coe v2) (coe v3) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_136 v10 v11 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_pair_76 v10 v11
                           (d_realize'45'infer_30
                              (coe v0) (coe v14) (coe v16) (coe v10) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe v17) (coe v11) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_144 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v10
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_neg_294
                    (d_realize'45'infer_30
                       (coe v0) (coe v10) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3)
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_156
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v11
               -> case coe v11 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v12 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_float_198
                           (MAlonzo.Code.Once.Float.Decimal.d_negate_22
                              (coe
                                 MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28 (coe v12) (coe v13)
                                 (coe v14)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_176 v9 v11 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v16 v17 v18
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_let''_178 v12 v13 v11 v9
                    (d_realize'45'infer_30
                       (coe v0) (coe v17) (coe v9) (coe v12) (coe v14))
                    (d_realize'45'infer_30
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_368
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                             (coe v16) (coe v9))
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'44'__16
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0))
                             (coe v9))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364 (coe v0))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_sigEffects_366 (coe v0)))
                       (coe v18) (coe v2)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v11 v13)
                       (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_206 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v22 v23 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_case''_146 v16 v17 v18 v14 v15
                    v11 v12
                    (d_realize'45'infer_30
                       (coe v0) (coe v22)
                       (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v11) (coe v12))
                       (coe v16) (coe v19))
                    (d_realize'45'infer_30
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_368
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                             (coe v23) (coe v11))
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'44'__16
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0))
                             (coe v11))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364 (coe v0))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_sigEffects_366 (coe v0)))
                       (coe v24) (coe v2)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v14 v17)
                       (coe v20))
                    (d_realize'45'infer_30
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_368
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                             (coe v25) (coe v12))
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'44'__16
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0))
                             (coe v12))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364 (coe v0))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_sigEffects_366 (coe v0)))
                       (coe v26) (coe v2)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v15 v18)
                       (coe v21))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_220 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v14 v15 v16
               -> case coe v14 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_add_208 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_sub_218 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_mul_228 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_div_276 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_mod''_286 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                              (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_234 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v14 v15 v16
               -> case coe v14 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fadd_238 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fsub_248 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fmul_258 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v10) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_248 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v14 v15 v16
               -> case coe v14 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fadd_238 v9 v10
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_266
                              (d_realize'45'infer_30
                                 (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                                 (coe v12)))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fsub_248 v9 v10
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_266
                              (d_realize'45'infer_30
                                 (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                                 (coe v12)))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fmul_258 v9 v10
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_266
                              (d_realize'45'infer_30
                                 (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                                 (coe v12)))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v10) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_262 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v14 v15 v16
               -> case coe v14 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fadd_238 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v9) (coe v12))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_266
                              (d_realize'45'infer_30
                                 (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                                 (coe v13)))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fsub_248 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v9) (coe v12))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_266
                              (d_realize'45'infer_30
                                 (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                                 (coe v13)))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fmul_258 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v9) (coe v12))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_266
                              (d_realize'45'infer_30
                                 (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                                 (coe v13)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_276 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v14 v15 v16
               -> case coe v14 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_lt_304 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_le_314 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_gt_324 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_ge_334 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_eq_344 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_ne_354 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                              (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_286 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_416 v8 v2
                    (coe MAlonzo.Code.Once.IR.C_id_22)
                    (d_realize'45'infer_30
                       (coe v0) (coe v11) (coe v2) (coe v8) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_298 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_416 v9
                    (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v2) (coe v8))
                    (coe MAlonzo.Code.Once.IR.C_fst_44)
                    (d_realize'45'infer_30
                       (coe v0) (coe v12)
                       (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v2) (coe v8))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_310 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_416 v9
                    (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v7) (coe v2))
                    (coe MAlonzo.Code.Once.IR.C_snd_50)
                    (d_realize'45'infer_30
                       (coe v0) (coe v12)
                       (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v7) (coe v2))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_320 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_416 v8 v7
                    (coe MAlonzo.Code.Once.IR.C_terminal_74)
                    (d_realize'45'infer_30
                       (coe v0) (coe v11) (coe v7) (coe v8) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_332 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_416 v9
                    (coe
                       MAlonzo.Code.Once.Type.C__'42'__122
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v7)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v2))
                       (coe v7))
                    (coe MAlonzo.Code.Once.IR.C_apply_92)
                    (d_realize'45'infer_30
                       (coe v0) (coe v12)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__122
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v7)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v2))
                          (coe v7))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_350 v8 v10 v11 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_app_48 v11 v12 v8 v10
                    (d_realize'45'infer_30
                       (coe v0) (coe v16)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v8)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v2))
                       (coe v11) (coe v14))
                    (d_realize_20 (coe v0) (coe v17) (coe v8) (coe v12) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_366 v8 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v17 v18 v19
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_effApp_62 v10 v11 v8
                           (d_realize'45'infer_30
                              (coe v0) (coe v15)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v8)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe MAlonzo.Code.Once.Type.C_eff_36))
                                 (coe v19))
                              (coe v10) (coe v13))
                           (d_realize_20 (coe v0) (coe v16) (coe v8) (coe v11) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Realize.realize-global
d_realize'45'global_40 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_realize'45'global_40 ~v0 v1 v2 ~v3 v4
  = du_realize'45'global_40 v1 v2 v4
du_realize'45'global_40 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_realize'45'global_40 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_372
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v5
               -> coe MAlonzo.Code.Once.Surface.Elaborate.du_intLit_8 (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'float_384
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v8 v9 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Elaborate.du_floatLit_20
                    (coe
                       MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28 (coe v8) (coe v9)
                       (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'int_390
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v6
               -> case coe v6 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v7
                      -> coe
                           MAlonzo.Code.Once.Surface.Elaborate.du_intLit_8
                           (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'float_402
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v9
               -> case coe v9 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v10 v11 v12 v13
                      -> coe
                           MAlonzo.Code.Once.Surface.Elaborate.du_floatLit_20
                           (coe
                              MAlonzo.Code.Once.Float.Decimal.d_negate_22
                              (coe
                                 MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28 (coe v10) (coe v11)
                                 (coe v12)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'terminal_406
        -> coe MAlonzo.Code.Once.IR.C_terminal_74
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_418 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v12 v13
                      -> coe
                           MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                           (coe du_realize'45'global_40 (coe v10) (coe v12) (coe v8))
                           (coe du_realize'45'global_40 (coe v11) (coe v13) (coe v9))
                           (coe MAlonzo.Code.Once.IR.C_Heap_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_428 v7
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v10 v11
                      -> coe
                           MAlonzo.Code.Once.IR.C__'8728'__30
                           (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v10))
                           (coe
                              MAlonzo.Code.Once.IR.C_inl_56 (coe MAlonzo.Code.Once.IR.C_Heap_8))
                           (coe du_realize'45'global_40 (coe v9) (coe v10) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_438 v7
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v10 v11
                      -> coe
                           MAlonzo.Code.Once.IR.C__'8728'__30
                           (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v11))
                           (coe
                              MAlonzo.Code.Once.IR.C_inr_62 (coe MAlonzo.Code.Once.IR.C_Heap_8))
                           (coe du_realize'45'global_40 (coe v9) (coe v11) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_448 v6 v8
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v11
                      -> coe
                           MAlonzo.Code.Once.IR.C__'8728'__30
                           (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68
                              (coe MAlonzo.Code.Once.IRTy.d_eraseF_40 (coe v11))
                              (coe
                                 MAlonzo.Code.Once.IRTy.C_μ'45'type_26
                                 (coe MAlonzo.Code.Once.IRTy.d_eraseF_40 (coe v11))))
                           (coe
                              MAlonzo.Code.Once.IR.C_In_96
                              (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                 (coe v11) (coe v6))
                              (coe MAlonzo.Code.Once.IR.C_Heap_8))
                           (coe
                              du_realize'45'global_40 (coe v10)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v11) (coe v1))
                              (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Realize.realize-morph
d_realize'45'morph_88 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_realize'45'morph_88 ~v0 v1 v2 v3 ~v4 v5
  = du_realize'45'morph_88 v1 v2 v3 v5
du_realize'45'morph_88 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_realize'45'morph_88 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_456
        -> coe MAlonzo.Code.Once.IR.C_id_22
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_466
        -> coe MAlonzo.Code.Once.IR.C_fst_44
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_476
        -> coe MAlonzo.Code.Once.IR.C_snd_50
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_484
        -> coe MAlonzo.Code.Once.IR.C_terminal_74
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_492
        -> coe MAlonzo.Code.Once.IR.C_initial_78
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_502
        -> coe
             MAlonzo.Code.Once.IR.C_inl_56 (coe MAlonzo.Code.Once.IR.C_Heap_8)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_512
        -> coe
             MAlonzo.Code.Once.IR.C_inr_62 (coe MAlonzo.Code.Once.IR.C_Heap_8)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_528 v8 v12 v13
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
                      -> coe
                           MAlonzo.Code.Once.IR.C__'8728'__30
                           (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v8))
                           (coe du_realize'45'morph_88 (coe v17) (coe v8) (coe v2) (coe v12))
                           (coe du_realize'45'morph_88 (coe v15) (coe v1) (coe v8) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_544 v11 v12
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> case coe v13 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
                      -> case coe v1 of
                           MAlonzo.Code.Once.Type.C__'43'__124 v17 v18
                             -> coe
                                  MAlonzo.Code.Once.IR.C_case_70
                                  (coe
                                     du_realize'45'morph_88 (coe v16) (coe v17) (coe v2) (coe v11))
                                  (coe
                                     du_realize'45'morph_88 (coe v14) (coe v18) (coe v2) (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'pair_558 v10 v11
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v12 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'42'__122 v16 v17
                             -> coe
                                  MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                                  (coe
                                     du_realize'45'morph_88 (coe v15) (coe v1) (coe v16) (coe v10))
                                  (coe
                                     du_realize'45'morph_88 (coe v13) (coe v1) (coe v17) (coe v11))
                                  (coe MAlonzo.Code.Once.IR.C_Heap_8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'curry_570 v9
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Once.IR.C_curry_86
                           (coe
                              du_realize'45'morph_88 (coe v11)
                              (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v1) (coe v12))
                              (coe v14) (coe v9))
                           (coe MAlonzo.Code.Once.IR.C_Heap_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'cata_584 v9 v11
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v14
                      -> coe
                           MAlonzo.Code.Once.IR.C_Cata_106
                           (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                              (coe v14) (coe v9))
                           (coe
                              du_realize'45'morph_88 (coe v13)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v14) (coe v2))
                              (coe v2) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596 v9
        -> coe du_realize'45'global_40 (coe v0) (coe v2) (coe v9)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named_608 v12 v13
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v14
               -> coe
                    MAlonzo.Code.Once.IR.C_SigOp_154 (coe v1) (coe v2)
                    (coe
                       MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_412 (coe v1)
                       (coe v2) (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v14))
                       (coe v12) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named'45'resolved_620 v10 v11
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v12
               -> coe
                    MAlonzo.Code.Once.IR.C_SigOp_154 (coe v1) (coe v2)
                    (coe
                       MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_412 (coe v1)
                       (coe v2) (coe v12) (coe v10) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
