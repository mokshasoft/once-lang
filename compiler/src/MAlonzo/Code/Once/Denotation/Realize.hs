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
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Sub
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
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_realize_20 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'check_420
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
             (coe MAlonzo.Code.Once.IR.C_id_20)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'check_430
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
             (coe MAlonzo.Code.Once.IR.C_fst_42)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'check_440
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
             (coe MAlonzo.Code.Once.IR.C_snd_48)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'morph'45'check_448
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
             (coe MAlonzo.Code.Once.IR.C_terminal_72)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'morph'45'check_456
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
             (coe MAlonzo.Code.Once.IR.C_initial_76)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'morph'45'check_466
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
             (coe MAlonzo.Code.Once.IR.C_inl_54)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'morph'45'check_476
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
             (coe MAlonzo.Code.Once.IR.C_inr_60)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'g_496 v9 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v20 v21 v22
                             -> case coe v21 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v23 v24
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_comp''_448 v12 v13 v9
                                         (d_realize_20
                                            (coe v0) (coe v19)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe v9)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v24))
                                               (coe v22))
                                            (coe v12) (coe v15))
                                         (d_realize'45'd_44
                                            (coe v0) (coe v17) (coe v20) (coe v9) (coe v24)
                                            (coe v13) (coe v14))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'f_520 v9 v11 v13 v14 v15 v16 v17 v18
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v21 v22
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v23 v24 v25
                             -> case coe v24 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v26 v27
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_comp''_448 v14 v15 v9
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe v9)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v13))
                                               (coe v11))
                                            v17
                                            (d_realize'45'infer_30
                                               (coe v0) (coe v22)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                  (coe v9)
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                     (coe v13))
                                                  (coe v11))
                                               (coe v14) (coe v16)))
                                         (d_realize_20
                                            (coe v0) (coe v20)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe v23)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v27))
                                               (coe v9))
                                            (coe v15) (coe v18))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'copair'45'check_540 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v20 v21 v22
                             -> case coe v20 of
                                  MAlonzo.Code.Once.Type.C__'43'__126 v23 v24
                                    -> case coe v21 of
                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50 v25 v26
                                           -> coe
                                                MAlonzo.Code.Once.Surface.Syntax.C_copair''_466 v12
                                                v13
                                                (d_realize_20
                                                   (coe v0) (coe v19)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                      (coe v23)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v26))
                                                      (coe v22))
                                                   (coe v12) (coe v14))
                                                (d_realize_20
                                                   (coe v0) (coe v17)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                      (coe v24)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v26))
                                                      (coe v22))
                                                   (coe v13) (coe v15))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'morph'45'check_560 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v20 v21 v22
                             -> case coe v21 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v23 v24
                                    -> case coe v22 of
                                         MAlonzo.Code.Once.Type.C__'42'__124 v25 v26
                                           -> coe
                                                MAlonzo.Code.Once.Surface.Syntax.C_fork''_484 v12
                                                v13
                                                (d_realize_20
                                                   (coe v0) (coe v19)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                      (coe v20)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v24))
                                                      (coe v25))
                                                   (coe v12) (coe v14))
                                                (d_realize_20
                                                   (coe v0) (coe v17)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                      (coe v20)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v24))
                                                      (coe v26))
                                                   (coe v13) (coe v15))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'curry'45'check_578 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v16 v17 v18
                      -> case coe v18 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v19 v20 v21
                             -> case coe v20 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v22 v23
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_curry''_502
                                         (d_realize_20
                                            (coe v0) (coe v15)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'42'__124 (coe v16)
                                                  (coe v19))
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v23))
                                               (coe v21))
                                            (coe v3) (coe v13))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'cata'45'check_592 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v15 v16 v17
                      -> case coe v15 of
                           MAlonzo.Code.Once.Type.C_μ'45'type_130 v18
                             -> case coe v16 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v19 v20
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_cata_516 v11
                                         (d_realize_20
                                            (coe v0) (coe v14)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe
                                                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170
                                                  (coe v18) (coe v17))
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v20))
                                               (coe v17))
                                            (coe v3) (coe v12))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'ana'45'check_606 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v15 v16 v17
                      -> case coe v17 of
                           MAlonzo.Code.Once.Type.C_ν'45'type_132 v18 v19
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_ana_530 v11
                                  (d_realize_20
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404
                                        (coe (0 :: Integer))
                                        (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                                        (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                        (coe (0 :: Integer))
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_imports_400
                                           (coe v0))
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_polys_402
                                           (coe v0)))
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v15)
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v19))
                                        (coe
                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v18)
                                           (coe v15)))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                        (coe (0 :: Integer)))
                                     (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v7 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_coerce_372 v7 v11
             (d_realize'45'infer_30
                (coe v0) (coe v1) (coe v7) (coe v3) (coe v10))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_638 v11 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v16 v17
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v18 v19 v20
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v11
                           (d_realize_20
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404
                                 (coe
                                    addInt (coe (1 :: Integer))
                                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_394 (coe v0))
                                    (coe v16) (coe v18))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_396 (coe v0))
                                    (coe v18))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398
                                    (coe v0))
                                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_400 (coe v0))
                                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_402 (coe v0)))
                              (coe v17) (coe v20)
                              (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v11 v3)
                              (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_654 v10 v11 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__124 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_pair_78 v10 v11
                           (d_realize_20 (coe v0) (coe v14) (coe v16) (coe v10) (coe v12))
                           (d_realize_20 (coe v0) (coe v15) (coe v17) (coe v11) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_664 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_130 v13
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v8
                           (MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v13) (coe v2))
                           (coe
                              MAlonzo.Code.Once.IR.C_In_94
                              (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                 (coe v13) (coe v9)))
                           (d_realize_20
                              (coe v0) (coe v12)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v13) (coe v2))
                              (coe v8) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_676 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v9
                    (coe
                       MAlonzo.Code.Once.Type.C__'42'__124
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v7)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v2))
                       (coe v7))
                    (coe MAlonzo.Code.Once.IR.C_apply_90)
                    (d_realize'45'infer_30
                       (coe v0) (coe v12)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__124
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v7)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v2))
                          (coe v7))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_688 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v9 v13
                           (coe MAlonzo.Code.Once.IR.C_inl_54)
                           (d_realize_20 (coe v0) (coe v12) (coe v13) (coe v9) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_700 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v9 v14
                           (coe MAlonzo.Code.Once.IR.C_inr_60)
                           (d_realize_20 (coe v0) (coe v12) (coe v14) (coe v9) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_710 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v8
                    (coe MAlonzo.Code.Once.Type.C_Void_122)
                    (coe MAlonzo.Code.Once.IR.C_initial_76)
                    (d_realize_20
                       (coe v0) (coe v11) (coe MAlonzo.Code.Once.Type.C_Void_122) (coe v8)
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_724 v8 v9 v10 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v16
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_398 v16
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Realize.realize-infer
d_realize'45'infer_30 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
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
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_int_186 v7
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_42
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v10 v11 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_float_194
                    (MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28
                       (coe v10) (coe v11) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_46
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_154
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_50
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_154
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_62 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.du_svar'8594'expr_540 (coe v9)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_72 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_sigOp_380
                    (MAlonzo.Code.Once.CanonicalName.d_bare_12
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20 v12
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             ("." :: Data.Text.Text) v11)))
                    v10
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_80 v8 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v11
               -> case coe v11 of
                    MAlonzo.Code.Once.CanonicalName.C_canonical_10 v12
                      -> let v13
                               = coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_380 v11 v10 in
                         coe
                           (case coe v12 of
                              (:) v14 v15
                                -> case coe v15 of
                                     [] -> coe MAlonzo.Code.Once.Surface.Syntax.C_closure_388 v14
                                     _ -> coe v13
                              _ -> coe v13)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_88 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v12
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_closure_388 v12
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_104 v8 v9 v10 v11 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v17
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_398 v17
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_114 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v11 v12
               -> coe d_realize_20 (coe v0) (coe v11) (coe v2) (coe v3) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_130 v10 v11 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__124 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_pair_78 v10 v11
                           (d_realize'45'infer_30
                              (coe v0) (coe v14) (coe v16) (coe v10) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe v17) (coe v11) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_138 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v10
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_neg_300
                    (d_realize'45'infer_30
                       (coe v0) (coe v10) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3)
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_150
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v11
               -> case coe v11 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v12 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_float_194
                           (MAlonzo.Code.Once.Float.Decimal.d_negate_22
                              (coe
                                 MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28 (coe v12) (coe v13)
                                 (coe v14)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_170 v9 v11 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v16 v17 v18
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_let''_180 v12 v13 v11 v9
                    (d_realize'45'infer_30
                       (coe v0) (coe v17) (coe v9) (coe v12) (coe v14))
                    (d_realize'45'infer_30
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_394 (coe v0))
                             (coe v16) (coe v9))
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'44'__16
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_396 (coe v0))
                             (coe v9))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_400 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_402 (coe v0)))
                       (coe v18) (coe v2)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v11 v13)
                       (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_200 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v22 v23 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_case''_148 v16 v17 v18 v14 v15
                    v11 v12
                    (d_realize'45'infer_30
                       (coe v0) (coe v22)
                       (coe MAlonzo.Code.Once.Type.C__'43'__126 (coe v11) (coe v12))
                       (coe v16) (coe v19))
                    (d_realize'45'infer_30
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_394 (coe v0))
                             (coe v23) (coe v11))
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'44'__16
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_396 (coe v0))
                             (coe v11))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_400 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_402 (coe v0)))
                       (coe v24) (coe v2)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v14 v17)
                       (coe v20))
                    (d_realize'45'infer_30
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_394 (coe v0))
                             (coe v25) (coe v12))
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'44'__16
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_396 (coe v0))
                             (coe v12))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_400 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_402 (coe v0)))
                       (coe v26) (coe v2)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v15 v18)
                       (coe v21))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_214 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v14 v15 v16
               -> case coe v14 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_add_204 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_sub_214 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_mul_224 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_div_282 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_mod''_292 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v10)
                              (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_228 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v14 v15 v16
               -> case coe v14 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fadd_234 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Float_136)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Float_136)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fsub_244 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Float_136)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Float_136)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fmul_254 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Float_136)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Float_136)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fdiv_264 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Float_136)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Float_136)
                              (coe v10) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_242 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v14 v15 v16
               -> case coe v14 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fadd_234 v9 v10
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_272
                              (d_realize'45'infer_30
                                 (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v9)
                                 (coe v12)))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Float_136)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fsub_244 v9 v10
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_272
                              (d_realize'45'infer_30
                                 (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v9)
                                 (coe v12)))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Float_136)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fmul_254 v9 v10
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_272
                              (d_realize'45'infer_30
                                 (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v9)
                                 (coe v12)))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Float_136)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fdiv_264 v9 v10
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_272
                              (d_realize'45'infer_30
                                 (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v9)
                                 (coe v12)))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Float_136)
                              (coe v10) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_256 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v14 v15 v16
               -> case coe v14 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fadd_234 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Float_136)
                              (coe v9) (coe v12))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_272
                              (d_realize'45'infer_30
                                 (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v10)
                                 (coe v13)))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fsub_244 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Float_136)
                              (coe v9) (coe v12))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_272
                              (d_realize'45'infer_30
                                 (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v10)
                                 (coe v13)))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fmul_254 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Float_136)
                              (coe v9) (coe v12))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_272
                              (d_realize'45'infer_30
                                 (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v10)
                                 (coe v13)))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fdiv_264 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Float_136)
                              (coe v9) (coe v12))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_272
                              (d_realize'45'infer_30
                                 (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v10)
                                 (coe v13)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_270 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v14 v15 v16
               -> case coe v14 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_lt_310 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_le_320 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_gt_330 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_ge_340 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_eq_350 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_ne_360 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v10)
                              (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_280 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v8 v2
                    (coe MAlonzo.Code.Once.IR.C_id_20)
                    (d_realize'45'infer_30
                       (coe v0) (coe v11) (coe v2) (coe v8) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_292 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v9
                    (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v2) (coe v8))
                    (coe MAlonzo.Code.Once.IR.C_fst_42)
                    (d_realize'45'infer_30
                       (coe v0) (coe v12)
                       (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v2) (coe v8))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_304 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v9
                    (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v7) (coe v2))
                    (coe MAlonzo.Code.Once.IR.C_snd_48)
                    (d_realize'45'infer_30
                       (coe v0) (coe v12)
                       (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v7) (coe v2))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_314 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v8 v7
                    (coe MAlonzo.Code.Once.IR.C_terminal_72)
                    (d_realize'45'infer_30
                       (coe v0) (coe v11) (coe v7) (coe v8) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_326 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v9
                    (coe
                       MAlonzo.Code.Once.Type.C__'42'__124
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v7)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v2))
                       (coe v7))
                    (coe MAlonzo.Code.Once.IR.C_apply_90)
                    (d_realize'45'infer_30
                       (coe v0) (coe v12)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__124
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v7)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v2))
                          (coe v7))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'eff'45'app'45'infer_338 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v9
                           (coe
                              MAlonzo.Code.Once.Type.C__'42'__124
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v7)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe MAlonzo.Code.Once.Type.C_eff_36))
                                 (coe v15))
                              (coe v7))
                           (coe
                              MAlonzo.Code.Once.IR.C_curry_84
                              (coe
                                 MAlonzo.Code.Once.IR.C__'8728'__28
                                 (coe
                                    MAlonzo.Code.Once.IRTy.C__'42'__20
                                    (coe
                                       MAlonzo.Code.Once.IRTy.C__'8667'__24
                                       (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v7))
                                       (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v15)))
                                    (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v7)))
                                 (coe MAlonzo.Code.Once.IR.C_apply_90)
                                 (coe MAlonzo.Code.Once.IR.C_fst_42)))
                           (d_realize'45'infer_30
                              (coe v0) (coe v12)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'42'__124
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v7)
                                    (coe
                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                       (coe MAlonzo.Code.Once.Type.C_eff_36))
                                    (coe v15))
                                 (coe v7))
                              (coe v9) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'app'45'infer_350 v7 v9 v10 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v9
                    (coe
                       MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v7)
                       (coe MAlonzo.Code.Once.Type.C_pure_34))
                    (coe
                       MAlonzo.Code.Once.IR.C_Out_110
                       (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                          (coe v7) (coe v10)))
                    (d_realize'45'infer_30
                       (coe v0) (coe v14)
                       (coe
                          MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v7)
                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                       (coe v9) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'eff'45'app'45'infer_362 v7 v9 v10 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v9
                    (coe
                       MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v7)
                       (coe MAlonzo.Code.Once.Type.C_eff_36))
                    (coe
                       MAlonzo.Code.Once.IR.C_curry_84
                       (coe
                          MAlonzo.Code.Once.IR.C__'8728'__28
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                             (coe
                                MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v7)
                                (coe MAlonzo.Code.Once.Type.C_eff_36)))
                          (coe
                             MAlonzo.Code.Once.IR.C_Out_110
                             (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                (coe v7) (coe v10)))
                          (coe MAlonzo.Code.Once.IR.C_fst_42)))
                    (d_realize'45'infer_30
                       (coe v0) (coe v14)
                       (coe
                          MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v7)
                          (coe MAlonzo.Code.Once.Type.C_eff_36))
                       (coe v9) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_380 v8 v10 v11 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_app_50 v11 v12 v8 v10
                    (d_realize'45'infer_30
                       (coe v0) (coe v16)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v8)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v2))
                       (coe v11) (coe v14))
                    (d_realize_20 (coe v0) (coe v17) (coe v8) (coe v12) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_396 v8 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v17 v18 v19
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_effApp_64 v10 v11 v8
                           (d_realize'45'infer_30
                              (coe v0) (coe v15)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v8)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe MAlonzo.Code.Once.Type.C_eff_36))
                                 (coe v19))
                              (coe v10) (coe v13))
                           (d_realize_20 (coe v0) (coe v16) (coe v8) (coe v11) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app'45'spine_412 v8 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_app_50 v10 v11 v8
                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                    (d_realize'45'd_44
                       (coe v0) (coe v15) (coe v8) (coe v2)
                       (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v10) (coe v14))
                    (d_realize'45'infer_30
                       (coe v0) (coe v16) (coe v8) (coe v11) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Realize.realize-d
d_realize'45'd_44 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_realize'45'd_44 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_742 v10 v13 v15 v16 v17
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
             (coe
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v10)
                (coe
                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                   (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v13))
                (coe v3))
             (coe
                MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_74 v16
                (MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170 (coe v3)) v17)
             (d_realize'45'infer_30
                (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v10)
                   (coe
                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                      (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v13))
                   (coe v3))
                (coe v5) (coe v15))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'poly_766 v12 v13 v14 v15 v16 v17 v22 v23 v24 v25
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v26
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
                    (coe
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                          (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v12))
                       (coe v3))
                    (coe
                       MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_74
                       (MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170 (coe v2))
                       (MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170 (coe v3)) v25)
                    (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_398 v26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'lam_784 v12 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v17 v18
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v12
                    (d_realize'45'infer_30
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_394 (coe v0))
                             (coe v17) (coe v2))
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'44'__16
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_396 (coe v0))
                             (coe v2))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_400 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_402 (coe v0)))
                       (coe v18) (coe v3)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v12 v5)
                       (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'compose_804 v11 v14 v15 v16 v17
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_comp''_448 v14 v15 v11
                           (d_realize'45'd_44
                              (coe v0) (coe v21) (coe v11) (coe v3) (coe v4) (coe v14) (coe v17))
                           (d_realize'45'd_44
                              (coe v0) (coe v19) (coe v2) (coe v11) (coe v4) (coe v15) (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'id_812
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
             (coe MAlonzo.Code.Once.IR.C_id_20)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst_822
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
             (coe MAlonzo.Code.Once.IR.C_fst_42)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd_832
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
             (coe MAlonzo.Code.Once.IR.C_snd_48)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'terminal_840
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
             (coe MAlonzo.Code.Once.IR.C_terminal_72)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'initial_846
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
             (coe MAlonzo.Code.Once.IR.C_initial_76)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case_866 v14 v15 v16 v17
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'43'__126 v22 v23
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_copair''_466 v14 v15
                                  (d_realize'45'd_44
                                     (coe v0) (coe v21) (coe v22) (coe v3) (coe v4) (coe v14)
                                     (coe v16))
                                  (d_realize'45'd_44
                                     (coe v0) (coe v19) (coe v23) (coe v3) (coe v4) (coe v15)
                                     (coe v17))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'pair_886 v14 v15 v16 v17
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
                      -> case coe v3 of
                           MAlonzo.Code.Once.Type.C__'42'__124 v22 v23
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_fork''_484 v14 v15
                                  (d_realize'45'd_44
                                     (coe v0) (coe v21) (coe v2) (coe v22) (coe v4) (coe v14)
                                     (coe v16))
                                  (d_realize'45'd_44
                                     (coe v0) (coe v19) (coe v2) (coe v23) (coe v4) (coe v15)
                                     (coe v17))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata_900 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_130 v17
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_cata_516 v13
                           (d_realize'45'infer_30
                              (coe v0) (coe v16)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                 (coe
                                    MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v17)
                                    (coe v3))
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
                                 (coe v3))
                              (coe v5) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
