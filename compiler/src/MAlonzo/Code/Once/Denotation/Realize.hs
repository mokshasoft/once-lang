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
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Typing
import qualified MAlonzo.Code.Once.Lang.Typing.Scope
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Surface.Syntax

-- Once.Denotation.Realize.poly-usage-eq
d_poly'45'usage'45'eq_8 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_poly'45'usage'45'eq_8 = erased
-- Once.Denotation.Realize.realize
d_realize_20 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_realize_20 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Typing.C_t'45'id'45'check_432 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
             (coe MAlonzo.Code.Once.IR.C_id_20)
      MAlonzo.Code.Once.Lang.Typing.C_t'45'fst'45'check_444 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
             (coe MAlonzo.Code.Once.IR.C_fst_42)
      MAlonzo.Code.Once.Lang.Typing.C_t'45'snd'45'check_456 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
             (coe MAlonzo.Code.Once.IR.C_snd_48)
      MAlonzo.Code.Once.Lang.Typing.C_t'45'terminal'45'morph'45'check_466 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
             (coe MAlonzo.Code.Once.IR.C_terminal_72)
      MAlonzo.Code.Once.Lang.Typing.C_t'45'initial'45'morph'45'check_476 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
             (coe MAlonzo.Code.Once.IR.C_initial_76)
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inl'45'morph'45'check_488 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
             (coe MAlonzo.Code.Once.IR.C_inl_54)
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inr'45'morph'45'check_500 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
             (coe MAlonzo.Code.Once.IR.C_inr_60)
      MAlonzo.Code.Once.Lang.Typing.C_t'45'compose'45'check'45'g_520 v9 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v18 v19
                      -> case coe v2 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v20 v21 v22
                             -> case coe v21 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v23 v24
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v12 v13 v9
                                         (d_realize_20
                                            (coe v0) (coe v19)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v9)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v24))
                                               (coe v22))
                                            (coe v12) (coe v15))
                                         (d_realize'45'd_44
                                            (coe v0) (coe v17) (coe v20) (coe v9) (coe v24)
                                            (coe v13) (coe v14))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'compose'45'check'45'f_544 v9 v11 v13 v14 v15 v16 v17 v18
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v21 v22
                      -> case coe v2 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v23 v24 v25
                             -> case coe v24 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v26 v27
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v14 v15 v9
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v9)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v13))
                                               (coe v11))
                                            v17
                                            (d_realize'45'infer_30
                                               (coe v0) (coe v22)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                  (coe v9)
                                                  (coe
                                                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                     (coe
                                                        MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                     (coe v13))
                                                  (coe v11))
                                               (coe v14) (coe v16)))
                                         (d_realize_20
                                            (coe v0) (coe v20)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v23)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v27))
                                               (coe v9))
                                            (coe v15) (coe v18))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'case'45'copair'45'check_564 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v18 v19
                      -> case coe v2 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v20 v21 v22
                             -> case coe v20 of
                                  MAlonzo.Code.Once.Lang.Type.C__'43'__26 v23 v24
                                    -> case coe v21 of
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v25 v26
                                           -> coe
                                                MAlonzo.Code.Once.Surface.Syntax.C_copair''_470 v12
                                                v13
                                                (d_realize_20
                                                   (coe v0) (coe v19)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                      (coe v23)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                         (coe v26))
                                                      (coe v22))
                                                   (coe v12) (coe v14))
                                                (d_realize_20
                                                   (coe v0) (coe v17)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                      (coe v24)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                         (coe v26))
                                                      (coe v22))
                                                   (coe v13) (coe v15))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'pair'45'morph'45'check_584 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v18 v19
                      -> case coe v2 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v20 v21 v22
                             -> case coe v21 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v23 v24
                                    -> case coe v22 of
                                         MAlonzo.Code.Once.Lang.Type.C__'42'__24 v25 v26
                                           -> coe
                                                MAlonzo.Code.Once.Surface.Syntax.C_fork''_488 v12
                                                v13
                                                (d_realize_20
                                                   (coe v0) (coe v19)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                      (coe v20)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                         (coe v24))
                                                      (coe v25))
                                                   (coe v12) (coe v14))
                                                (d_realize_20
                                                   (coe v0) (coe v17)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                      (coe v20)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                         (coe v24))
                                                      (coe v26))
                                                   (coe v13) (coe v15))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'curry'45'check_604 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v17 v18 v19
                      -> case coe v19 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v20 v21 v22
                             -> case coe v21 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v23 v24
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_curry''_506
                                         (d_realize_20
                                            (coe v0) (coe v16)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v17)
                                                  (coe v20))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v24))
                                               (coe v22))
                                            (coe v3) (coe v14))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'cata'45'check_620 v10 v11 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v16 v17 v18
                      -> case coe v16 of
                           MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v19
                             -> case coe v17 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v20 v21
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v10 v12
                                         (d_realize_20
                                            (coe v0) (coe v15)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                                                  (coe v19) (coe v18))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v21))
                                               (coe v18))
                                            (coe v10) (coe v13))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'ana'45'check_640 v11 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v16 v17
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v18 v19 v20
                      -> case coe v20 of
                           MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v21 v22
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_ana_536 v11 v14
                                  (d_realize_20
                                     (coe v0) (coe v17)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v18)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.Grade.d_fin_46 (coe v22)))
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                                           (coe v21) (coe v18)))
                                     (coe v11) (coe v15))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'loop'45'check_652 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_loop_548 v9
                           (d_realize_20
                              (coe v0) (coe v12)
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                                 (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v15) (coe v13)))
                              (coe v9) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_664 v7 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v7 v11
             (d_realize'45'infer_30
                (coe v0) (coe v1) (coe v7) (coe v3) (coe v10))
      MAlonzo.Code.Once.Lang.Typing.C_t'45'lam_686 v11 v14 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 v17 v18
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v19 v20 v21
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v11
                           (d_realize_20
                              (coe
                                 MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                                 (coe
                                    addInt (coe (1 :: Integer))
                                    (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v0)))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Typing.Scope.d_extendCtx_26
                                    (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_named_120 (coe v0))
                                    (coe v17) (coe v19))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du__'44'__16
                                    (coe
                                       MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v0))
                                    (coe v19))
                                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_imports_124 (coe v0))
                                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_polys_126 (coe v0))
                                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_sig_128 (coe v0)))
                              (coe v18) (coe v21)
                              (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v11 v3)
                              (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'pair'45'lit'45'check_702 v10 v11 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RPair_48 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_pair_82 v10 v11
                           (d_realize_20 (coe v0) (coe v14) (coe v16) (coe v10) (coe v12))
                           (d_realize_20 (coe v0) (coe v15) (coe v17) (coe v11) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'In'45'app'45'check_712 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v13
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v8
                           (MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                              (coe v13) (coe v2))
                           (coe
                              MAlonzo.Code.Once.IR.C_In_94
                              (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                 (coe v13) (coe v9)))
                           (d_realize_20
                              (coe v0) (coe v12)
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v13)
                                 (coe v2))
                              (coe v8) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'check_724 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v9
                    (coe
                       MAlonzo.Code.Once.Lang.Type.C__'42'__24
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                          (coe v2))
                       (coe v7))
                    (coe MAlonzo.Code.Once.IR.C_apply_90)
                    (d_realize'45'infer_30
                       (coe v0) (coe v12)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'42'__24
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                             (coe v2))
                          (coe v7))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inl'45'app'45'check_736 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v9 v13
                           (coe MAlonzo.Code.Once.IR.C_inl_54)
                           (d_realize_20 (coe v0) (coe v12) (coe v13) (coe v9) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inr'45'app'45'check_748 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v9 v14
                           (coe MAlonzo.Code.Once.IR.C_inr_60)
                           (d_realize_20 (coe v0) (coe v12) (coe v14) (coe v9) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'initial'45'app'45'check_758 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v8
                    (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
                    (coe MAlonzo.Code.Once.IR.C_initial_76)
                    (d_realize_20
                       (coe v0) (coe v11) (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
                       (coe v8) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'poly'45'instantiate_772 v8 v9 v10 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 v16
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v16
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Realize.realize-infer
d_realize'45'infer_30 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_realize'45'infer_30 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Typing.C_t'45'int_30
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RInt_54 v7
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_int_190 v7
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'float_42
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RFloat_56 v10 v11 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_float_198
                    (MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30
                       (coe v10) (coe v11) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'unit_46
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_158
      MAlonzo.Code.Once.Lang.Typing.C_t'45'unit'45'var_50
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_158
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'local_62 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.du_svar'8594'expr_558 (coe v9)
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved_70 v8 v9 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40 v12
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v12 v11
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'own_78
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40 v10
               -> case coe v10 of
                    MAlonzo.Code.Once.Spec.Name.C_canonical_12 v11
                      -> case coe v11 of
                           (:) v12 v13
                             -> coe MAlonzo.Code.Once.Surface.Syntax.C_closure_392 v12
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'import_86 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 v12
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_closure_392 v12
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'poly'45'instantiate'45'infer_102 v8 v9 v10 v11 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 v17
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v17
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'annot_112 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RAnnot_58 v11 v12
               -> coe d_realize_20 (coe v0) (coe v11) (coe v2) (coe v3) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'pair_128 v10 v11 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RPair_48 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_pair_82 v10 v11
                           (d_realize'45'infer_30
                              (coe v0) (coe v14) (coe v16) (coe v10) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe v17) (coe v11) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'neg_136 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RUnaryOp_62 v10
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_neg_304
                    (d_realize'45'infer_30
                       (coe v0) (coe v10) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                       (coe v3) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'neg'45'float_148
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RUnaryOp_62 v11
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RFloat_56 v12 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_float_198
                           (MAlonzo.Code.Once.Spec.Float.Decimal.d_negate_24
                              (coe
                                 MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30 (coe v12)
                                 (coe v13) (coe v14)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'let_168 v9 v11 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RLet_46 v16 v17 v18
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_let''_184 v12 v13 v11 v9
                    (d_realize'45'infer_30
                       (coe v0) (coe v17) (coe v9) (coe v12) (coe v14))
                    (d_realize'45'infer_30
                       (coe
                          MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.Lang.Typing.Scope.d_extendCtx_26
                             (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_named_120 (coe v0))
                             (coe v16) (coe v9))
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'44'__16
                             (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v0))
                             (coe v9))
                          (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_imports_124 (coe v0))
                          (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_polys_126 (coe v0))
                          (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_sig_128 (coe v0)))
                       (coe v18) (coe v2)
                       (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v11 v13)
                       (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'case_202 v11 v12 v13 v14 v16 v17 v18 v19 v20 v21 v22 v23 v24
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RDestruct_50 v25 v26 v27 v28 v29
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_case''_152 v18 v19 v20 v16 v17
                    v11 v12
                    (d_realize'45'infer_30
                       (coe v0) (coe v25)
                       (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v11) (coe v12))
                       (coe v18) (coe v21))
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v13
                       (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
                          (coe v13) (coe v2)
                          (coe MAlonzo.Code.Once.Lang.Type.Sub.d_left_256 (coe v24)))
                       (d_realize'45'infer_30
                          (coe
                             MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                             (coe
                                addInt (coe (1 :: Integer))
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v0)))
                             (coe
                                MAlonzo.Code.Once.Lang.Typing.Scope.d_extendCtx_26
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_named_120 (coe v0))
                                (coe v26) (coe v11))
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'44'__16
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v0))
                                (coe v11))
                             (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_imports_124 (coe v0))
                             (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_polys_126 (coe v0))
                             (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_sig_128 (coe v0)))
                          (coe v27) (coe v13)
                          (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v16 v19)
                          (coe v22)))
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v14
                       (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
                          (coe v14) (coe v2)
                          (coe MAlonzo.Code.Once.Lang.Type.Sub.d_right_258 (coe v24)))
                       (d_realize'45'infer_30
                          (coe
                             MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                             (coe
                                addInt (coe (1 :: Integer))
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v0)))
                             (coe
                                MAlonzo.Code.Once.Lang.Typing.Scope.d_extendCtx_26
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_named_120 (coe v0))
                                (coe v28) (coe v12))
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'44'__16
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v0))
                                (coe v12))
                             (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_imports_124 (coe v0))
                             (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_polys_126 (coe v0))
                             (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_sig_128 (coe v0)))
                          (coe v29) (coe v14)
                          (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v17 v20)
                          (coe v23)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith_216 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60 v14 v15 v16
               -> case coe v14 of
                    MAlonzo.Code.Once.Lang.Syntax.C_OpAdd_8
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_add_208 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpSub_10
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_sub_218 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpMul_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_mul_228 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpDiv_14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_div_286 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpMod_16
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_mod''_296 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                              (coe v10) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float_230 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60 v14 v15 v16
               -> case coe v14 of
                    MAlonzo.Code.Once.Lang.Syntax.C_OpAdd_8
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fadd_238 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpSub_10
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fsub_248 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpMul_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fmul_258 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpDiv_14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                              (coe v10) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float'45'il_244 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60 v14 v15 v16
               -> case coe v14 of
                    MAlonzo.Code.Once.Lang.Syntax.C_OpAdd_8
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fadd_238 v9 v10
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                              (d_realize'45'infer_30
                                 (coe v0) (coe v15) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                 (coe v9) (coe v12)))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpSub_10
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fsub_248 v9 v10
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                              (d_realize'45'infer_30
                                 (coe v0) (coe v15) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                 (coe v9) (coe v12)))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpMul_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fmul_258 v9 v10
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                              (d_realize'45'infer_30
                                 (coe v0) (coe v15) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                 (coe v9) (coe v12)))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpDiv_14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268 v9 v10
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                              (d_realize'45'infer_30
                                 (coe v0) (coe v15) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                 (coe v9) (coe v12)))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                              (coe v10) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float'45'ir_258 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60 v14 v15 v16
               -> case coe v14 of
                    MAlonzo.Code.Once.Lang.Syntax.C_OpAdd_8
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fadd_238 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                              (coe v9) (coe v12))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                              (d_realize'45'infer_30
                                 (coe v0) (coe v16) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                 (coe v10) (coe v13)))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpSub_10
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fsub_248 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                              (coe v9) (coe v12))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                              (d_realize'45'infer_30
                                 (coe v0) (coe v16) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                 (coe v10) (coe v13)))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpMul_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fmul_258 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                              (coe v9) (coe v12))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                              (d_realize'45'infer_30
                                 (coe v0) (coe v16) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                 (coe v10) (coe v13)))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpDiv_14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                              (coe v9) (coe v12))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                              (d_realize'45'infer_30
                                 (coe v0) (coe v16) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                 (coe v10) (coe v13)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'cmp_272 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60 v14 v15 v16
               -> case coe v14 of
                    MAlonzo.Code.Once.Lang.Syntax.C_OpLt_18
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_lt_314 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpLe_20
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_le_324 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpGt_22
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_gt_334 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpGe_24
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_ge_344 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpEq_26
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_eq_354 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                              (coe v10) (coe v13))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpNe_28
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_ne_364 v9 v10
                           (d_realize'45'infer_30
                              (coe v0) (coe v15) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                              (coe v9) (coe v12))
                           (d_realize'45'infer_30
                              (coe v0) (coe v16) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                              (coe v10) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'id'45'app_282 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v8 v2
                    (coe MAlonzo.Code.Once.IR.C_id_20)
                    (d_realize'45'infer_30
                       (coe v0) (coe v11) (coe v2) (coe v8) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'fst'45'app_294 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v9
                    (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v2) (coe v8))
                    (coe MAlonzo.Code.Once.IR.C_fst_42)
                    (d_realize'45'infer_30
                       (coe v0) (coe v12)
                       (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v2) (coe v8))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'snd'45'app_306 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v9
                    (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v7) (coe v2))
                    (coe MAlonzo.Code.Once.IR.C_snd_48)
                    (d_realize'45'infer_30
                       (coe v0) (coe v12)
                       (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v7) (coe v2))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'terminal'45'app_316 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v8 v7
                    (coe MAlonzo.Code.Once.IR.C_terminal_72)
                    (d_realize'45'infer_30
                       (coe v0) (coe v11) (coe v7) (coe v8) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'app'45'infer_328 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v9
                    (coe
                       MAlonzo.Code.Once.Lang.Type.C__'42'__24
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                          (coe v2))
                       (coe v7))
                    (coe MAlonzo.Code.Once.IR.C_apply_90)
                    (d_realize'45'infer_30
                       (coe v0) (coe v12)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'42'__24
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                             (coe v2))
                          (coe v7))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'eff'45'app'45'infer_344 v7 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v15 v16 v17
                      -> case coe v16 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v18 v19
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v9
                                  (coe
                                     MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v19))
                                        (coe v17))
                                     (coe v7))
                                  (coe
                                     MAlonzo.Code.Once.IR.C_curry_84
                                     (coe
                                        MAlonzo.Code.Once.IR.C__'8728'__28
                                        (coe
                                           MAlonzo.Code.Once.IRTy.C__'42'__20
                                           (coe
                                              MAlonzo.Code.Once.IRTy.C__'8667'__24
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v7))
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                 (coe v17)))
                                           (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v7)))
                                        (coe MAlonzo.Code.Once.IR.C_apply_90)
                                        (coe MAlonzo.Code.Once.IR.C_fst_42)))
                                  (d_realize'45'infer_30
                                     (coe v0) (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                           (coe v7)
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                              (coe v19))
                                           (coe v17))
                                        (coe v7))
                                     (coe v9) (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'app'45'infer_356 v7 v9 v10 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v9
                    (coe
                       MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v7)
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42))
                    (coe
                       MAlonzo.Code.Once.IR.C_Out_110
                       (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                          (coe v7) (coe v10)))
                    (d_realize'45'infer_30
                       (coe v0) (coe v14)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v7)
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42))
                       (coe v9) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'eff'45'app'45'infer_368 v7 v9 v10 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v9
                    (coe
                       MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v7)
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_44))
                    (coe
                       MAlonzo.Code.Once.IR.C_curry_84
                       (coe
                          MAlonzo.Code.Once.IR.C__'8728'__28
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v7)
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_44)))
                          (coe
                             MAlonzo.Code.Once.IR.C_Out_110
                             (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                (coe v7) (coe v10)))
                          (coe MAlonzo.Code.Once.IR.C_fst_42)))
                    (d_realize'45'infer_30
                       (coe v0) (coe v14)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v7)
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_44))
                       (coe v9) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'app_386 v8 v10 v11 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v16 v17
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_app_50 v11 v12 v8 v10
                    (d_realize'45'infer_30
                       (coe v0) (coe v16)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v8)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 (coe v10)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                          (coe v2))
                       (coe v11) (coe v14))
                    (d_realize_20 (coe v0) (coe v17) (coe v8) (coe v12) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'effApp_406 v8 v10 v11 v13 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v17 v18
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v19 v20 v21
                      -> case coe v20 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v22 v23
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_effApp_68 v10 v11 v8 v13
                                  (d_realize'45'infer_30
                                     (coe v0) (coe v17)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v8)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v23))
                                        (coe v21))
                                     (coe v10) (coe v15))
                                  (d_realize_20 (coe v0) (coe v18) (coe v8) (coe v11) (coe v16))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'app'45'spine_422 v8 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_app_50 v10 v11 v8
                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                    (d_realize'45'd_44
                       (coe v0) (coe v15) (coe v8) (coe v2)
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) (coe v10)
                       (coe v14))
                    (d_realize'45'infer_30
                       (coe v0) (coe v16) (coe v8) (coe v11) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Realize.realize-d
d_realize'45'd_44 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_realize'45'd_44 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_790 v10 v13 v15 v16 v17
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
             (coe
                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v10)
                (coe
                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v13))
                (coe v3))
             (coe
                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v16
                (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v3))
                v17)
             (d_realize'45'infer_30
                (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v10)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v13))
                   (coe v3))
                (coe v5) (coe v15))
      MAlonzo.Code.Once.Lang.Typing.C_d'45'poly_814 v12 v13 v14 v15 v16 v17 v22 v23 v24 v25
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 v26
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                    (coe
                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v12))
                       (coe v3))
                    (coe
                       MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                       (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v2))
                       (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v3))
                       v25)
                    (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'lam_834 v12 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 v17 v18
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v12
                    (d_realize'45'infer_30
                       (coe
                          MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.Lang.Typing.Scope.d_extendCtx_26
                             (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_named_120 (coe v0))
                             (coe v17) (coe v2))
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'44'__16
                             (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v0))
                             (coe v2))
                          (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_imports_124 (coe v0))
                          (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_polys_126 (coe v0))
                          (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_sig_128 (coe v0)))
                       (coe v18) (coe v3)
                       (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v12 v5)
                       (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'compose_854 v11 v14 v15 v16 v17
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v20 v21
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v14 v15 v11
                           (d_realize'45'd_44
                              (coe v0) (coe v21) (coe v11) (coe v3) (coe v4) (coe v14) (coe v17))
                           (d_realize'45'd_44
                              (coe v0) (coe v19) (coe v2) (coe v11) (coe v4) (coe v15) (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'id_864 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
             (coe MAlonzo.Code.Once.IR.C_id_20)
      MAlonzo.Code.Once.Lang.Typing.C_d'45'fst_876 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
             (coe MAlonzo.Code.Once.IR.C_fst_42)
      MAlonzo.Code.Once.Lang.Typing.C_d'45'snd_888 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
             (coe MAlonzo.Code.Once.IR.C_snd_48)
      MAlonzo.Code.Once.Lang.Typing.C_d'45'terminal_898 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
             (coe MAlonzo.Code.Once.IR.C_terminal_72)
      MAlonzo.Code.Once.Lang.Typing.C_d'45'initial_906 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
             (coe MAlonzo.Code.Once.IR.C_initial_76)
      MAlonzo.Code.Once.Lang.Typing.C_d'45'case_930 v12 v13 v16 v17 v18 v19 v20
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v21 v22
               -> case coe v21 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v23 v24
                      -> case coe v2 of
                           MAlonzo.Code.Once.Lang.Type.C__'43'__26 v25 v26
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_copair''_470 v16 v17
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v25)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v4))
                                        (coe v12))
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                        (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                           (coe v25))
                                        (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
                                           (coe v12) (coe v3)
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.Sub.d_left_256 (coe v20)))
                                        (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94
                                           (coe v4)))
                                     (d_realize'45'd_44
                                        (coe v0) (coe v24) (coe v25) (coe v12) (coe v4) (coe v16)
                                        (coe v18)))
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v26)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v4))
                                        (coe v13))
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                        (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                           (coe v26))
                                        (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
                                           (coe v13) (coe v3)
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.Sub.d_right_258
                                              (coe v20)))
                                        (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94
                                           (coe v4)))
                                     (d_realize'45'd_44
                                        (coe v0) (coe v22) (coe v26) (coe v13) (coe v4) (coe v17)
                                        (coe v19)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'pair_950 v14 v15 v16 v17
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v20 v21
                      -> case coe v3 of
                           MAlonzo.Code.Once.Lang.Type.C__'42'__24 v22 v23
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_fork''_488 v14 v15
                                  (d_realize'45'd_44
                                     (coe v0) (coe v21) (coe v2) (coe v22) (coe v4) (coe v14)
                                     (coe v16))
                                  (d_realize'45'd_44
                                     (coe v0) (coe v19) (coe v2) (coe v23) (coe v4) (coe v15)
                                     (coe v17))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'cata_966 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v16 v17
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v18
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v12 v14
                           (d_realize'45'infer_30
                              (coe v0) (coe v17)
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v18)
                                    (coe v3))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v4))
                                 (coe v3))
                              (coe v12) (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
