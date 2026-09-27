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
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Seq
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
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_realize_20 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'check_540
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
             (coe MAlonzo.Code.Once.IR.C_id_20)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'check_550
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
             (coe MAlonzo.Code.Once.IR.C_fst_42)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'check_560
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
             (coe MAlonzo.Code.Once.IR.C_snd_48)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'morph'45'check_568
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
             (coe MAlonzo.Code.Once.IR.C_terminal_72)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'morph'45'check_576
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
             (coe MAlonzo.Code.Once.IR.C_initial_76)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'morph'45'check_586
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
             (coe MAlonzo.Code.Once.IR.C_inl_54)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'morph'45'check_596
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
             (coe MAlonzo.Code.Once.IR.C_inr_60)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'g_616 v9 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v20 v21 v22
                             -> case coe v21 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v23 v24
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_comp''_446 v12 v13 v9
                                         (d_realize_20
                                            (coe v0) (coe v19)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'f_640 v9 v11 v13 v14 v15 v16 v17 v18
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v21 v22
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v23 v24 v25
                             -> case coe v24 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v26 v27
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_comp''_446 v14 v15 v9
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_coerce_378
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                               (coe v9)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v13))
                                               (coe v11))
                                            v17
                                            (d_realize'45'infer_30
                                               (coe v0) (coe v22)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
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
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'copair'45'check_660 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v20 v21 v22
                             -> case coe v20 of
                                  MAlonzo.Code.Once.Type.C__'43'__124 v23 v24
                                    -> case coe v21 of
                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50 v25 v26
                                           -> coe
                                                MAlonzo.Code.Once.Surface.Syntax.C_copair''_464 v12
                                                v13
                                                (d_realize_20
                                                   (coe v0) (coe v19)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
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
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'morph'45'check_680 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v20 v21 v22
                             -> case coe v21 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v23 v24
                                    -> case coe v22 of
                                         MAlonzo.Code.Once.Type.C__'42'__122 v25 v26
                                           -> coe
                                                MAlonzo.Code.Once.Surface.Syntax.C_fork''_482 v12
                                                v13
                                                (d_realize_20
                                                   (coe v0) (coe v19)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
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
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'curry'45'check_698 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v16 v17 v18
                      -> case coe v18 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v19 v20 v21
                             -> case coe v20 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v22 v23
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_curry''_500
                                         (d_realize_20
                                            (coe v0) (coe v15)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'42'__122 (coe v16)
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'cata'45'check_710 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v14 v15 v16
                      -> case coe v14 of
                           MAlonzo.Code.Once.Type.C_μ'45'type_128 v17
                             -> case coe v15 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_cata_512 v10
                                         (d_realize_20
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_330
                                               (coe (0 :: Integer))
                                               (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                                               (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                               (coe (0 :: Integer))
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326
                                                  (coe v0))
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_polys_328
                                                  (coe v0)))
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                               (coe
                                                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                  (coe v17) (coe v16))
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v19))
                                               (coe v16))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                               (coe (0 :: Integer)))
                                            (coe v11))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'ana'45'check_724 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
                      -> case coe v17 of
                           MAlonzo.Code.Once.Type.C_ν'45'type_130 v18 v19
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_ana_526 v11
                                  (d_realize_20
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_330
                                        (coe (0 :: Integer))
                                        (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                                        (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                        (coe (0 :: Integer))
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326
                                           (coe v0))
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_polys_328
                                           (coe v0)))
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v15)
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v19))
                                        (coe
                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v18)
                                           (coe v15)))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                        (coe (0 :: Integer)))
                                     (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_736 v7 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_coerce_378 v7 v11
             (d_realize'45'infer_30
                (coe v0) (coe v1) (coe v7) (coe v3) (coe v10))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_756 v11 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v16 v17
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v18 v19 v20
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v11
                           (d_realize_20
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_330
                                 (coe
                                    addInt (coe (1 :: Integer))
                                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_320 (coe v0))
                                    (coe v16) (coe v18))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_322 (coe v0))
                                    (coe v18))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324
                                    (coe v0))
                                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326 (coe v0))
                                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_328 (coe v0)))
                              (coe v17) (coe v20)
                              (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v11 v3)
                              (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_772 v10 v11 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_pair_78 v10 v11
                           (d_realize_20 (coe v0) (coe v14) (coe v16) (coe v10) (coe v12))
                           (d_realize_20 (coe v0) (coe v15) (coe v17) (coe v11) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_782 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v13
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v8
                           (MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v13) (coe v2))
                           (coe
                              MAlonzo.Code.Once.IR.C_In_94
                              (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                 (coe v13) (coe v9)))
                           (d_realize_20
                              (coe v0) (coe v12)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v13) (coe v2))
                              (coe v8) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_794 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v9
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
                    (coe MAlonzo.Code.Once.IR.C_apply_90)
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_806 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v9 v13
                           (coe MAlonzo.Code.Once.IR.C_inl_54)
                           (d_realize_20 (coe v0) (coe v12) (coe v13) (coe v9) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_818 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v9 v14
                           (coe MAlonzo.Code.Once.IR.C_inr_60)
                           (d_realize_20 (coe v0) (coe v12) (coe v14) (coe v9) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_828 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v8
                    (coe MAlonzo.Code.Once.Type.C_Void_120)
                    (coe MAlonzo.Code.Once.IR.C_initial_76)
                    (d_realize_20
                       (coe v0) (coe v11) (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v8)
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_842 v8 v9 v10 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428
             (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
             (coe MAlonzo.Code.Once.Type.C_Unit_118)
             (coe
                MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_390
                (coe (0 :: Integer))
                (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                      (coe
                         MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_338
                         (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326 (coe v0))
                         (coe v10))))
                (coe v2)
                (coe
                   d_realize_20
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_330
                      (coe (0 :: Integer))
                      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                      (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                      (coe (0 :: Integer))
                      (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326 (coe v0))
                      (coe v10))
                   (coe v9) (coe v2)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                      (coe
                         MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                         (coe
                            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_338
                            (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326 (coe v0))
                            (coe v10))))
                   (coe v15)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_154)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Realize.realize-infer
d_realize'45'infer_30 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
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
                    MAlonzo.Code.Once.Surface.Syntax.C_float_200
                    (MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28
                       (coe v10) (coe v11) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_48
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v7
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_str_192 v7
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_52
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_154
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_56
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_154
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_68 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.du_svar'8594'expr_536 (coe v9)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_78 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_sigOp_386
                    (MAlonzo.Code.Once.CanonicalName.d_bare_12
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20 v13
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             ("." :: Data.Text.Text) v12)))
                    v10
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_86 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v12
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_386 v12 v10
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_94 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_sigOp_386
                    (MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v13)) v11
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_110 v8 v9 v10 v11 v15 v17
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428
             (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
             (coe MAlonzo.Code.Once.Type.C_Unit_118)
             (coe
                MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_390
                (coe (0 :: Integer))
                (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                      (coe
                         MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_338
                         (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326 (coe v0))
                         (coe v10))))
                (coe v2)
                (coe
                   d_realize_20
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_330
                      (coe (0 :: Integer))
                      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                      (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                      (coe (0 :: Integer))
                      (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326 (coe v0))
                      (coe v10))
                   (coe v9) (coe v2)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                      (coe
                         MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                         (coe
                            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_338
                            (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326 (coe v0))
                            (coe v10))))
                   (coe v17)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_154)
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
                           MAlonzo.Code.Once.Surface.Syntax.C_pair_78 v10 v11
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
                    MAlonzo.Code.Once.Surface.Syntax.C_neg_306
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
                           MAlonzo.Code.Once.Surface.Syntax.C_float_200
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
                    MAlonzo.Code.Once.Surface.Syntax.C_let''_180 v12 v13 v11 v9
                    (d_realize'45'infer_30
                       (coe v0) (coe v17) (coe v9) (coe v12) (coe v14))
                    (d_realize'45'infer_30
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_330
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_320 (coe v0))
                             (coe v16) (coe v9))
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'44'__16
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_322 (coe v0))
                             (coe v9))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_328 (coe v0)))
                       (coe v18) (coe v2)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v11 v13)
                       (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_206 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v22 v23 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_case''_148 v16 v17 v18 v14 v15
                    v11 v12
                    (d_realize'45'infer_30
                       (coe v0) (coe v22)
                       (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v11) (coe v12))
                       (coe v16) (coe v19))
                    (d_realize'45'infer_30
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_330
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_320 (coe v0))
                             (coe v23) (coe v11))
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'44'__16
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_322 (coe v0))
                             (coe v11))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_328 (coe v0)))
                       (coe v24) (coe v2)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v14 v17)
                       (coe v20))
                    (d_realize'45'infer_30
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_330
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_320 (coe v0))
                             (coe v25) (coe v12))
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'44'__16
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_322 (coe v0))
                             (coe v12))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_328 (coe v0)))
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
                           MAlonzo.Code.Once.Surface.Syntax.C_add_210 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_sub_220 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_mul_230 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_div_288 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_mod''_298 v9 v10
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
                           MAlonzo.Code.Once.Surface.Syntax.C_fadd_240 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fsub_250 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fmul_260 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fdiv_270 v9 v10
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
                           MAlonzo.Code.Once.Surface.Syntax.C_fadd_240 v9 v10
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_278
                              (d_realize'45'infer_30
                                 (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                                 (coe v12)))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fsub_250 v9 v10
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_278
                              (d_realize'45'infer_30
                                 (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                                 (coe v12)))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fmul_260 v9 v10
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_278
                              (d_realize'45'infer_30
                                 (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                                 (coe v12)))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fdiv_270 v9 v10
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_278
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
                           MAlonzo.Code.Once.Surface.Syntax.C_fadd_240 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v9) (coe v12))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_278
                              (d_realize'45'infer_30
                                 (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                                 (coe v13)))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fsub_250 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v9) (coe v12))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_278
                              (d_realize'45'infer_30
                                 (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                                 (coe v13)))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fmul_260 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v9) (coe v12))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_278
                              (d_realize'45'infer_30
                                 (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                                 (coe v13)))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fdiv_270 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Float_134)
                              (coe v9) (coe v12))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_278
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
                           MAlonzo.Code.Once.Surface.Syntax.C_lt_316 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_le_326 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_gt_336 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_ge_346 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_eq_356 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9)
                              (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10)
                              (coe v13))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_ne_366 v9 v10
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
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v8 v2
                    (coe MAlonzo.Code.Once.IR.C_id_20)
                    (d_realize'45'infer_30
                       (coe v0) (coe v11) (coe v2) (coe v8) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_298 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v9
                    (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v2) (coe v8))
                    (coe MAlonzo.Code.Once.IR.C_fst_42)
                    (d_realize'45'infer_30
                       (coe v0) (coe v12)
                       (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v2) (coe v8))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_310 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v9
                    (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v7) (coe v2))
                    (coe MAlonzo.Code.Once.IR.C_snd_48)
                    (d_realize'45'infer_30
                       (coe v0) (coe v12)
                       (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v7) (coe v2))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_320 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v8 v7
                    (coe MAlonzo.Code.Once.IR.C_terminal_72)
                    (d_realize'45'infer_30
                       (coe v0) (coe v11) (coe v7) (coe v8) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_332 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v9
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
                    (coe MAlonzo.Code.Once.IR.C_apply_90)
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'eff'45'app'45'infer_344 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v9
                           (coe
                              MAlonzo.Code.Once.Type.C__'42'__122
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v7)
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
                                       (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v7))
                                       (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v15)))
                                    (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v7)))
                                 (coe MAlonzo.Code.Once.IR.C_apply_90)
                                 (coe MAlonzo.Code.Once.IR.C_fst_42)))
                           (d_realize'45'infer_30
                              (coe v0) (coe v12)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'42'__122
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v7)
                                    (coe
                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                       (coe MAlonzo.Code.Once.Type.C_eff_36))
                                    (coe v15))
                                 (coe v7))
                              (coe v9) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'app'45'infer_356 v7 v9 v10 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v9
                    (coe
                       MAlonzo.Code.Once.Type.C_ν'45'type_130 (coe v7)
                       (coe MAlonzo.Code.Once.Type.C_pure_34))
                    (coe
                       MAlonzo.Code.Once.IR.C_Out_110
                       (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                          (coe v7) (coe v10)))
                    (d_realize'45'infer_30
                       (coe v0) (coe v14)
                       (coe
                          MAlonzo.Code.Once.Type.C_ν'45'type_130 (coe v7)
                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                       (coe v9) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'eff'45'app'45'infer_368 v7 v9 v10 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v9
                    (coe
                       MAlonzo.Code.Once.Type.C_ν'45'type_130 (coe v7)
                       (coe MAlonzo.Code.Once.Type.C_eff_36))
                    (coe
                       MAlonzo.Code.Once.IR.C_curry_84
                       (coe
                          MAlonzo.Code.Once.IR.C__'8728'__28
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                             (coe
                                MAlonzo.Code.Once.Type.C_ν'45'type_130 (coe v7)
                                (coe MAlonzo.Code.Once.Type.C_eff_36)))
                          (coe
                             MAlonzo.Code.Once.IR.C_Out_110
                             (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                (coe v7) (coe v10)))
                          (coe MAlonzo.Code.Once.IR.C_fst_42)))
                    (d_realize'45'infer_30
                       (coe v0) (coe v14)
                       (coe
                          MAlonzo.Code.Once.Type.C_ν'45'type_130 (coe v7)
                          (coe MAlonzo.Code.Once.Type.C_eff_36))
                       (coe v9) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_386 v8 v10 v11 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_app_50 v11 v12 v8 v10
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_402 v8 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v17 v18 v19
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_effApp_64 v10 v11 v8
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app'45'spine_418 v8 v10 v11 v13 v14
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'void_426 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v10
               -> coe
                    d_realize'45'infer_30 (coe v0) (coe v10)
                    (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v3) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'void_454 v11 v12 v13 v14 v16 v17 v18 v19 v20
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v21 v22 v23 v24 v25
               -> coe
                    d_realize'45'infer_30 (coe v0) (coe v21)
                    (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v3) (coe v18)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'void'45'l_470 v9 v11 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v14 v15 v16
               -> coe
                    d_realize'45'infer_30 (coe v0) (coe v15)
                    (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v3) (coe v12)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'void'45'r_486 v9 v10 v11 v12 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v15 v16 v17
               -> coe
                    MAlonzo.Code.Once.Surface.Seq.du_seq_18 (coe v10) (coe v11)
                    (coe v9)
                    (coe
                       d_realize'45'infer_30 (coe v0) (coe v16) (coe v9) (coe v10)
                       (coe v12))
                    (coe
                       d_realize'45'infer_30 (coe v0) (coe v17)
                       (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v11) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app'45'void_494 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v7
                    (coe MAlonzo.Code.Once.Type.C_Void_120)
                    (coe MAlonzo.Code.Once.IR.C_initial_76)
                    (d_realize'45'infer_30
                       (coe v0) (coe v10) (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v7)
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app'45'void_502 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v7
                    (coe MAlonzo.Code.Once.Type.C_Void_120)
                    (coe MAlonzo.Code.Once.IR.C_initial_76)
                    (d_realize'45'infer_30
                       (coe v0) (coe v10) (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v7)
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'void_510 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v7
                    (coe MAlonzo.Code.Once.Type.C_Void_120)
                    (coe MAlonzo.Code.Once.IR.C_initial_76)
                    (d_realize'45'infer_30
                       (coe v0) (coe v10) (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v7)
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'app'45'void_518 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v7
                    (coe MAlonzo.Code.Once.Type.C_Void_120)
                    (coe MAlonzo.Code.Once.IR.C_initial_76)
                    (d_realize'45'infer_30
                       (coe v0) (coe v10) (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v7)
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app'45'void_532 v8 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> coe
                    d_realize'45'infer_30 (coe v0) (coe v14)
                    (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v3) (coe v12)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Realize.realize-d
d_realize'45'd_44 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_realize'45'd_44 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v10 v13 v15 v16 v17
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_coerce_378
             (coe
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v10)
                (coe
                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                   (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v13))
                (coe v3))
             (coe
                MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_74 v16
                (MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_164 (coe v3)) v17)
             (d_realize'45'infer_30
                (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v10)
                   (coe
                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                      (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v13))
                   (coe v3))
                (coe v5) (coe v15))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'lam_878 v12 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v17 v18
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v12
                    (d_realize'45'infer_30
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_330
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_320 (coe v0))
                             (coe v17) (coe v2))
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'44'__16
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_322 (coe v0))
                             (coe v2))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_328 (coe v0)))
                       (coe v18) (coe v3)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v12 v5)
                       (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'compose_898 v11 v14 v15 v16 v17
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_comp''_446 v14 v15 v11
                           (d_realize'45'd_44
                              (coe v0) (coe v21) (coe v11) (coe v3) (coe v4) (coe v14) (coe v17))
                           (d_realize'45'd_44
                              (coe v0) (coe v19) (coe v2) (coe v11) (coe v4) (coe v15) (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'id_906
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
             (coe MAlonzo.Code.Once.IR.C_id_20)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst_916
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
             (coe MAlonzo.Code.Once.IR.C_fst_42)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd_926
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
             (coe MAlonzo.Code.Once.IR.C_snd_48)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'terminal_934
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
             (coe MAlonzo.Code.Once.IR.C_terminal_72)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'initial_940
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
             (coe MAlonzo.Code.Once.IR.C_initial_76)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case_960 v14 v15 v16 v17
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'43'__124 v22 v23
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_copair''_464 v14 v15
                                  (d_realize'45'd_44
                                     (coe v0) (coe v21) (coe v22) (coe v3) (coe v4) (coe v14)
                                     (coe v16))
                                  (d_realize'45'd_44
                                     (coe v0) (coe v19) (coe v23) (coe v3) (coe v4) (coe v15)
                                     (coe v17))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'pair_980 v14 v15 v16 v17
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
                      -> case coe v3 of
                           MAlonzo.Code.Once.Type.C__'42'__122 v22 v23
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_fork''_482 v14 v15
                                  (d_realize'45'd_44
                                     (coe v0) (coe v21) (coe v2) (coe v22) (coe v4) (coe v14)
                                     (coe v16))
                                  (d_realize'45'd_44
                                     (coe v0) (coe v19) (coe v2) (coe v23) (coe v4) (coe v15)
                                     (coe v17))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata_992 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v16
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_cata_512 v12
                           (d_realize'45'infer_30
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_330
                                 (coe (0 :: Integer))
                                 (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                                 (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                 (coe (0 :: Integer))
                                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326 (coe v0))
                                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_328 (coe v0)))
                              (coe v15)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                 (coe
                                    MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v16)
                                    (coe v3))
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
                                 (coe v3))
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                 (coe (0 :: Integer)))
                              (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst'45'void_998
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
             (coe MAlonzo.Code.Once.IR.C_initial_76)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd'45'void_1004
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
             (coe MAlonzo.Code.Once.IR.C_initial_76)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case'45'void_1022 v10 v11 v13 v14 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
                      -> coe
                           MAlonzo.Code.Once.Surface.Seq.du_seq_18 (coe v13) (coe v14)
                           (coe
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                              (coe MAlonzo.Code.Once.Type.C_Void_120)
                              (coe
                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                 (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
                              (coe v10))
                           (coe
                              d_realize'45'd_44 (coe v0) (coe v20)
                              (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v10) (coe v4)
                              (coe v13) (coe v15))
                           (coe
                              MAlonzo.Code.Once.Surface.Seq.du_seq0_34
                              (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0))
                              (coe v14)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                 (coe MAlonzo.Code.Once.Type.C_Void_120)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
                                 (coe v11))
                              (coe
                                 d_realize'45'd_44 (coe v0) (coe v18)
                                 (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v11) (coe v4)
                                 (coe v14) (coe v16))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
                                 (coe MAlonzo.Code.Once.IR.C_initial_76)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata'45'void_1032 v9 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Seq.du_seq0_34
                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0))
                    (coe
                       MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                       (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                    (coe v9)
                    (coe
                       MAlonzo.Code.Once.Surface.Seq.du_embedClosed_60
                       (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0))
                       (coe v9)
                       (coe
                          d_realize'45'infer_30
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_330
                             (coe (0 :: Integer))
                             (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                             (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                             (coe (0 :: Integer))
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326 (coe v0))
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_328 (coe v0)))
                          (coe v13) (coe v9)
                          (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62) (coe v11)))
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
                       (coe MAlonzo.Code.Once.IR.C_initial_76))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
