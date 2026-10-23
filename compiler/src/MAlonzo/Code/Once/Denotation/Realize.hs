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
import qualified MAlonzo.Code.Once.Internal.Type.Sub
import qualified MAlonzo.Code.Once.Internal.Typing
import qualified MAlonzo.Code.Once.Internal.Typing.Scope
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Surface.Syntax

-- Once.Denotation.Realize.poly-usage-eq
d_poly'45'usage'45'eq_8 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_poly'45'usage'45'eq_8 = erased
-- Once.Denotation.Realize.realize
d_realize_22 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__20 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_realize_22 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Internal.Typing.C_t'45'id'45'check_436 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_id_20)
      MAlonzo.Code.Once.Internal.Typing.C_t'45'fst'45'check_448 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_fst_42)
      MAlonzo.Code.Once.Internal.Typing.C_t'45'snd'45'check_460 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_snd_48)
      MAlonzo.Code.Once.Internal.Typing.C_t'45'terminal'45'morph'45'check_470 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_terminal_72)
      MAlonzo.Code.Once.Internal.Typing.C_t'45'initial'45'morph'45'check_480 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_initial_76)
      MAlonzo.Code.Once.Internal.Typing.C_t'45'inl'45'morph'45'check_492 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_inl_54)
      MAlonzo.Code.Once.Internal.Typing.C_t'45'inr'45'morph'45'check_504 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_inr_60)
      MAlonzo.Code.Once.Internal.Typing.C_t'45'compose'45'check'45'g_524 v10 v13 v14 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v19 v20
                      -> case coe v3 of
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v21 v22 v23
                             -> case coe v22 of
                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v24 v25
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_comp''_456 v13 v14 v10
                                         (d_realize_22
                                            (coe v0) (coe v1) (coe v20)
                                            (coe
                                               MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                               (coe v10)
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v25))
                                               (coe v23))
                                            (coe v13) (coe v16))
                                         (d_realize'45'd_50
                                            (coe v0) (coe v1) (coe v18) (coe v21) (coe v10)
                                            (coe v25) (coe v14) (coe v15))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'compose'45'check'45'f_548 v10 v12 v14 v15 v16 v17 v18 v19
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v20 v21
               -> case coe v20 of
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v22 v23
                      -> case coe v3 of
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v24 v25 v26
                             -> case coe v25 of
                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v27 v28
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_comp''_456 v15 v16 v10
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                                            (coe
                                               MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                               (coe v10)
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v14))
                                               (coe v12))
                                            v18
                                            (d_realize'45'infer_34
                                               (coe v0) (coe v1) (coe v23)
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                  (coe v10)
                                                  (coe
                                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                     (coe v14))
                                                  (coe v12))
                                               (coe v15) (coe v17)))
                                         (d_realize_22
                                            (coe v0) (coe v1) (coe v21)
                                            (coe
                                               MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                               (coe v24)
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v28))
                                               (coe v10))
                                            (coe v16) (coe v19))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'case'45'copair'45'check_568 v13 v14 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v19 v20
                      -> case coe v3 of
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v21 v22 v23
                             -> case coe v21 of
                                  MAlonzo.Code.Once.Spec.Type.C__'43'__24 v24 v25
                                    -> case coe v22 of
                                         MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v26 v27
                                           -> coe
                                                MAlonzo.Code.Once.Surface.Syntax.C_copair''_474 v13
                                                v14
                                                (d_realize_22
                                                   (coe v0) (coe v1) (coe v20)
                                                   (coe
                                                      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                      (coe v24)
                                                      (coe
                                                         MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                         (coe
                                                            MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                         (coe v27))
                                                      (coe v23))
                                                   (coe v13) (coe v15))
                                                (d_realize_22
                                                   (coe v0) (coe v1) (coe v18)
                                                   (coe
                                                      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                      (coe v25)
                                                      (coe
                                                         MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                         (coe
                                                            MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                         (coe v27))
                                                      (coe v23))
                                                   (coe v14) (coe v16))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'pair'45'morph'45'check_588 v13 v14 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v19 v20
                      -> case coe v3 of
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v21 v22 v23
                             -> case coe v22 of
                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v24 v25
                                    -> case coe v23 of
                                         MAlonzo.Code.Once.Spec.Type.C__'42'__22 v26 v27
                                           -> coe
                                                MAlonzo.Code.Once.Surface.Syntax.C_fork''_492 v13
                                                v14
                                                (d_realize_22
                                                   (coe v0) (coe v1) (coe v20)
                                                   (coe
                                                      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                      (coe v21)
                                                      (coe
                                                         MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                         (coe
                                                            MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                         (coe v25))
                                                      (coe v26))
                                                   (coe v13) (coe v15))
                                                (d_realize_22
                                                   (coe v0) (coe v1) (coe v18)
                                                   (coe
                                                      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                      (coe v21)
                                                      (coe
                                                         MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                         (coe
                                                            MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                         (coe v25))
                                                      (coe v27))
                                                   (coe v14) (coe v16))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'curry'45'check_608 v14 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v16 v17
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v18 v19 v20
                      -> case coe v20 of
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v21 v22 v23
                             -> case coe v22 of
                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v24 v25
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_curry''_510
                                         (d_realize_22
                                            (coe v0) (coe v1) (coe v17)
                                            (coe
                                               MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v18)
                                                  (coe v21))
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v25))
                                               (coe v23))
                                            (coe v4) (coe v15))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'cata'45'check_624 v11 v12 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v15 v16
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
                      -> case coe v17 of
                           MAlonzo.Code.Once.Spec.Type.C_μ_28 v20
                             -> case coe v18 of
                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v21 v22
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_cata_526 v11
                                         (MAlonzo.Code.Once.Internal.Typing.Scope.d_kinds_144
                                            (coe v1))
                                         v13
                                         (d_realize_22
                                            (coe v0) (coe v1) (coe v16)
                                            (coe
                                               MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50
                                                  (coe v20) (coe v19))
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v22))
                                               (coe v19))
                                            (coe v11) (coe v14))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'ana'45'check_644 v12 v13 v14 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v17 v18
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v19 v20 v21
                      -> case coe v21 of
                           MAlonzo.Code.Once.Spec.Type.C_ν_30 v22 v23
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_ana_544 v12
                                  (MAlonzo.Code.Once.Internal.Typing.Scope.d_kinds_144 (coe v1)) v15
                                  (d_realize_22
                                     (coe v0) (coe v1) (coe v18)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v19)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v23)))
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50
                                           (coe v22) (coe v19)))
                                     (coe v12) (coe v16))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'loop'45'check_656 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v12 v13
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v14 v15 v16
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_loop_556 v10
                           (d_realize_22
                              (coe v0) (coe v1) (coe v13)
                              (coe
                                 MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v14)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
                                 (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v16) (coe v14)))
                              (coe v10) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'sub_668 v8 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v8 v12
             (d_realize'45'infer_34
                (coe v0) (coe v1) (coe v2) (coe v8) (coe v4) (coe v11))
      MAlonzo.Code.Once.Internal.Typing.C_t'45'lam_690 v12 v15 v17
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 v18 v19
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v20 v21 v22
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_lam_38 v12
                           (d_realize_22
                              (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Internal.Typing.Scope.C_mkCtx_146
                                 (coe
                                    addInt (coe (1 :: Integer))
                                    (coe
                                       MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                                 (coe
                                    MAlonzo.Code.Once.Internal.Typing.Scope.du_extendCtx_34
                                    (coe
                                       MAlonzo.Code.Once.Internal.Typing.Scope.d_named_134 (coe v1))
                                    (coe v18) (coe v20))
                                 (coe
                                    MAlonzo.Code.Once.Spec.Context.C__'9656'__16
                                    (MAlonzo.Code.Once.Internal.Typing.Scope.d_debruijn_136
                                       (coe v1))
                                    v20)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Typing.Scope.d_imports_138 (coe v1))
                                 (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_polys_140 (coe v1))
                                 (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_sig_142 (coe v1))
                                 (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_kinds_144 (coe v1)))
                              (coe v19) (coe v22)
                              (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v12 v4)
                              (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'pair'45'lit'45'check_706 v11 v12 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_82 v15 v16
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Type.C__'42'__22 v17 v18
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_pair_86 v11 v12
                           (d_realize_22
                              (coe v0) (coe v1) (coe v15) (coe v17) (coe v11) (coe v13))
                           (d_realize_22
                              (coe v0) (coe v1) (coe v16) (coe v18) (coe v12) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'In'45'app'45'check_716 v9 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v12 v13
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Type.C_μ_28 v14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v9
                           (coe
                              MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v14)
                              (coe v3))
                           (coe
                              MAlonzo.Code.Once.IR.C_In_94
                              (coe
                                 MAlonzo.Code.Once.IRTy.WF.du_wf'45''8970''8971'_54 (coe v14)
                                 (coe v10)))
                           (d_realize_22
                              (coe v0) (coe v1) (coe v13)
                              (coe
                                 MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v14)
                                 (coe v3))
                              (coe v9) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'apply'45'check_728 v8 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v10
                    (coe
                       MAlonzo.Code.Once.Spec.Type.C__'42'__22
                       (coe
                          MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v8)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                          (coe v3))
                       (coe v8))
                    (coe MAlonzo.Code.Once.IR.C_apply_90)
                    (d_realize'45'infer_34
                       (coe v0) (coe v1) (coe v13)
                       (coe
                          MAlonzo.Code.Once.Spec.Type.C__'42'__22
                          (coe
                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v8)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                (coe
                                   MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                   (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                             (coe v3))
                          (coe v8))
                       (coe v10) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'inl'45'app'45'check_740 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v12 v13
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v10 v14
                           (coe MAlonzo.Code.Once.IR.C_inl_54)
                           (d_realize_22
                              (coe v0) (coe v1) (coe v13) (coe v14) (coe v10) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'inr'45'app'45'check_752 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v12 v13
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v10 v15
                           (coe MAlonzo.Code.Once.IR.C_inr_60)
                           (d_realize_22
                              (coe v0) (coe v1) (coe v13) (coe v15) (coe v10) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'initial'45'app'45'check_762 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v9
                    (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
                    (coe MAlonzo.Code.Once.IR.C_initial_76)
                    (d_realize_22
                       (coe v0) (coe v1) (coe v12)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Void_20) (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'poly'45'instantiate_776 v9 v10 v11 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v17
               -> case coe v17 of
                    MAlonzo.Code.Once.Spec.Name.C_canonical_12 v18
                      -> case coe v18 of
                           (:) v19 v20 -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_406 v19
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Realize.realize-infer
d_realize'45'infer_34 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_realize'45'infer_34 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Internal.Typing.C_t'45'int_38
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_88 v8
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_int_194 v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'float_48
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_90 v10 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_float_202
                    (MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30
                       (coe v10) (coe v11) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'unit_52
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_162
      MAlonzo.Code.Once.Internal.Typing.C_t'45'unit'45'var_56
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_162
      MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'local_68 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.du_svar'8594'expr_568 (coe v10)
      MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'resolved_78 v8 v10 v11 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v15
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_388 v8 v15 v13
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'own_88 v8
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v13
               -> case coe v13 of
                    MAlonzo.Code.Once.Spec.Name.C_canonical_12 v14
                      -> case coe v14 of
                           (:) v15 v16
                             -> coe MAlonzo.Code.Once.Surface.Syntax.C_closure_396 v15
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'poly'45'instantiate'45'infer_104 v9 v10 v11 v12 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v18
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Name.C_canonical_12 v19
                      -> case coe v19 of
                           (:) v20 v21 -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_406 v20
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'annot_116 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_92 v13 v14
               -> coe
                    d_realize_22 (coe v0) (coe v1) (coe v13) (coe v3) (coe v4)
                    (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'pair_132 v11 v12 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_82 v15 v16
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Type.C__'42'__22 v17 v18
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_pair_86 v11 v12
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v15) (coe v17) (coe v11) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16) (coe v18) (coe v12) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'neg_140 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_96 v10
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_neg_308
                    (d_realize'45'infer_34
                       (coe v0) (coe v1) (coe v10)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v4) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'neg'45'float_150
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_96 v10
               -> case coe v10 of
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_90 v11 v12 v13
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_float_202
                           (MAlonzo.Code.Once.Spec.Float.Decimal.d_negate_24
                              (coe
                                 MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30 (coe v11)
                                 (coe v12) (coe v13)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'let_170 v10 v12 v13 v14 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_80 v17 v18 v19
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_let''_188 v13 v14 v12 v10
                    (d_realize'45'infer_34
                       (coe v0) (coe v1) (coe v18) (coe v10) (coe v13) (coe v15))
                    (d_realize'45'infer_34
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Internal.Typing.Scope.C_mkCtx_146
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                          (coe
                             MAlonzo.Code.Once.Internal.Typing.Scope.du_extendCtx_34
                             (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_named_134 (coe v1))
                             (coe v17) (coe v10))
                          (coe
                             MAlonzo.Code.Once.Spec.Context.C__'9656'__16
                             (MAlonzo.Code.Once.Internal.Typing.Scope.d_debruijn_136 (coe v1))
                             v10)
                          (coe
                             MAlonzo.Code.Once.Internal.Typing.Scope.d_imports_138 (coe v1))
                          (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_polys_140 (coe v1))
                          (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_sig_142 (coe v1))
                          (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_kinds_144 (coe v1)))
                       (coe v19) (coe v3)
                       (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v12 v14)
                       (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'case_204 v12 v13 v14 v15 v17 v18 v19 v20 v21 v22 v23 v24 v25
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_84 v26 v27 v28 v29 v30
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_case''_156 v19 v20 v21 v17 v18
                    v12 v13
                    (d_realize'45'infer_34
                       (coe v0) (coe v1) (coe v26)
                       (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v12) (coe v13))
                       (coe v19) (coe v22))
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v14
                       (coe
                          MAlonzo.Code.Once.Internal.Type.Sub.du_'60''58''7580''8658''60''58'_92
                          (coe v14) (coe v3)
                          (coe MAlonzo.Code.Once.Spec.Sub.d_left_166 (coe v25)))
                       (d_realize'45'infer_34
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.Internal.Typing.Scope.C_mkCtx_146
                             (coe
                                addInt (coe (1 :: Integer))
                                (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                             (coe
                                MAlonzo.Code.Once.Internal.Typing.Scope.du_extendCtx_34
                                (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_named_134 (coe v1))
                                (coe v27) (coe v12))
                             (coe
                                MAlonzo.Code.Once.Spec.Context.C__'9656'__16
                                (MAlonzo.Code.Once.Internal.Typing.Scope.d_debruijn_136 (coe v1))
                                v12)
                             (coe
                                MAlonzo.Code.Once.Internal.Typing.Scope.d_imports_138 (coe v1))
                             (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_polys_140 (coe v1))
                             (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_sig_142 (coe v1))
                             (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_kinds_144 (coe v1)))
                          (coe v28) (coe v14)
                          (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v17 v20)
                          (coe v23)))
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v15
                       (coe
                          MAlonzo.Code.Once.Internal.Type.Sub.du_'60''58''7580''8658''60''58'_92
                          (coe v15) (coe v3)
                          (coe MAlonzo.Code.Once.Spec.Sub.d_right_168 (coe v25)))
                       (d_realize'45'infer_34
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.Internal.Typing.Scope.C_mkCtx_146
                             (coe
                                addInt (coe (1 :: Integer))
                                (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                             (coe
                                MAlonzo.Code.Once.Internal.Typing.Scope.du_extendCtx_34
                                (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_named_134 (coe v1))
                                (coe v29) (coe v13))
                             (coe
                                MAlonzo.Code.Once.Spec.Context.C__'9656'__16
                                (MAlonzo.Code.Once.Internal.Typing.Scope.d_debruijn_136 (coe v1))
                                v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Typing.Scope.d_imports_138 (coe v1))
                             (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_polys_140 (coe v1))
                             (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_sig_142 (coe v1))
                             (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_kinds_144 (coe v1)))
                          (coe v30) (coe v15)
                          (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v18 v21)
                          (coe v24)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith_218 v10 v11 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_94 v15 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpAdd_46
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_add_212 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpSub_48
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_sub_222 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMul_50
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_mul_232 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpDiv_52
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_div_290 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMod_54
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_mod''_300 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float_232 v10 v11 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_94 v15 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpAdd_46
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fadd_242 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpSub_48
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fsub_252 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMul_50
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fmul_262 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpDiv_52
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fdiv_272 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v11) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'il_246 v10 v11 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_94 v15 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpAdd_46
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fadd_242 v10 v11
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_280
                              (d_realize'45'infer_34
                                 (coe v0) (coe v1) (coe v16)
                                 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13)))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpSub_48
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fsub_252 v10 v11
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_280
                              (d_realize'45'infer_34
                                 (coe v0) (coe v1) (coe v16)
                                 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13)))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMul_50
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fmul_262 v10 v11
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_280
                              (d_realize'45'infer_34
                                 (coe v0) (coe v1) (coe v16)
                                 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13)))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpDiv_52
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fdiv_272 v10 v11
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_280
                              (d_realize'45'infer_34
                                 (coe v0) (coe v1) (coe v16)
                                 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13)))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v11) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'ir_260 v10 v11 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_94 v15 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpAdd_46
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fadd_242 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v10) (coe v13))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_280
                              (d_realize'45'infer_34
                                 (coe v0) (coe v1) (coe v17)
                                 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14)))
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpSub_48
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fsub_252 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v10) (coe v13))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_280
                              (d_realize'45'infer_34
                                 (coe v0) (coe v1) (coe v17)
                                 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14)))
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMul_50
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fmul_262 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v10) (coe v13))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_280
                              (d_realize'45'infer_34
                                 (coe v0) (coe v1) (coe v17)
                                 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14)))
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpDiv_52
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fdiv_272 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v10) (coe v13))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_i2f_280
                              (d_realize'45'infer_34
                                 (coe v0) (coe v1) (coe v17)
                                 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'cmp_274 v10 v11 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_94 v15 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLt_56
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_lt_318 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLe_58
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_le_328 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGt_60
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_gt_338 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGe_62
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_ge_348 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpEq_64
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_eq_358 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpNe_66
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_ne_368 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'id'45'app_284 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v9 v3
                    (coe MAlonzo.Code.Once.IR.C_id_20)
                    (d_realize'45'infer_34
                       (coe v0) (coe v1) (coe v12) (coe v3) (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'fst'45'app_296 v9 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v10
                    (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v3) (coe v9))
                    (coe MAlonzo.Code.Once.IR.C_fst_42)
                    (d_realize'45'infer_34
                       (coe v0) (coe v1) (coe v13)
                       (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v3) (coe v9))
                       (coe v10) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'snd'45'app_308 v8 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v10
                    (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v8) (coe v3))
                    (coe MAlonzo.Code.Once.IR.C_snd_48)
                    (d_realize'45'infer_34
                       (coe v0) (coe v1) (coe v13)
                       (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v8) (coe v3))
                       (coe v10) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'terminal'45'app_318 v8 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v9 v8
                    (coe MAlonzo.Code.Once.IR.C_terminal_72)
                    (d_realize'45'infer_34
                       (coe v0) (coe v1) (coe v12) (coe v8) (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'apply'45'app'45'infer_330 v8 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v10
                    (coe
                       MAlonzo.Code.Once.Spec.Type.C__'42'__22
                       (coe
                          MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v8)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                          (coe v3))
                       (coe v8))
                    (coe MAlonzo.Code.Once.IR.C_apply_90)
                    (d_realize'45'infer_34
                       (coe v0) (coe v1) (coe v13)
                       (coe
                          MAlonzo.Code.Once.Spec.Type.C__'42'__22
                          (coe
                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v8)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                (coe
                                   MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                   (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                             (coe v3))
                          (coe v8))
                       (coe v10) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'apply'45'eff'45'app'45'infer_346 v8 v10 v12 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v14 v15
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v16 v17 v18
                      -> case coe v17 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v19 v20
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v10
                                  (coe
                                     MAlonzo.Code.Once.Spec.Type.C__'42'__22
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v8)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v20))
                                        (coe v18))
                                     (coe v8))
                                  (coe
                                     MAlonzo.Code.Once.IR.C_curry_84
                                     (coe
                                        MAlonzo.Code.Once.IR.C__'8728'__28
                                        (coe
                                           MAlonzo.Code.Once.IRTy.C__'42'__20
                                           (coe
                                              MAlonzo.Code.Once.IRTy.C__'8667'__24
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                                 (coe v8))
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                                 (coe v18)))
                                           (coe
                                              MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                              (coe v8)))
                                        (coe MAlonzo.Code.Once.IR.C_apply_90)
                                        (coe MAlonzo.Code.Once.IR.C_fst_42)))
                                  (d_realize'45'infer_34
                                     (coe v0) (coe v1) (coe v15)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'42'__22
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                           (coe v8)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                              (coe v20))
                                           (coe v18))
                                        (coe v8))
                                     (coe v10) (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'Out'45'app'45'infer_358 v8 v10 v11 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v10
                    (coe
                       MAlonzo.Code.Once.Spec.Type.C_ν_30 (coe v8)
                       (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
                    (coe
                       MAlonzo.Code.Once.IR.C_Out_110
                       (coe
                          MAlonzo.Code.Once.IRTy.WF.du_wf'45''8970''8971'_54 (coe v8)
                          (coe v11)))
                    (d_realize'45'infer_34
                       (coe v0) (coe v1) (coe v15)
                       (coe
                          MAlonzo.Code.Once.Spec.Type.C_ν_30 (coe v8)
                          (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
                       (coe v10) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'Out'45'eff'45'app'45'infer_370 v8 v10 v11 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v10
                    (coe
                       MAlonzo.Code.Once.Spec.Type.C_ν_30 (coe v8)
                       (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38))
                    (coe
                       MAlonzo.Code.Once.IR.C_curry_84
                       (coe
                          MAlonzo.Code.Once.IR.C__'8728'__28
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                             (coe v0)
                             (coe
                                MAlonzo.Code.Once.Spec.Type.C_ν_30 (coe v8)
                                (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
                          (coe
                             MAlonzo.Code.Once.IR.C_Out_110
                             (coe
                                MAlonzo.Code.Once.IRTy.WF.du_wf'45''8970''8971'_54 (coe v8)
                                (coe v11)))
                          (coe MAlonzo.Code.Once.IR.C_fst_42)))
                    (d_realize'45'infer_34
                       (coe v0) (coe v1) (coe v15)
                       (coe
                          MAlonzo.Code.Once.Spec.Type.C_ν_30 (coe v8)
                          (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38))
                       (coe v10) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'app_388 v9 v11 v12 v13 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v17 v18
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_app_54 v12 v13 v9 v11
                    (d_realize'45'infer_34
                       (coe v0) (coe v1) (coe v17)
                       (coe
                          MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v9)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v11)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                          (coe v3))
                       (coe v12) (coe v15))
                    (d_realize_22
                       (coe v0) (coe v1) (coe v18) (coe v9) (coe v13) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'effApp_408 v9 v11 v12 v14 v16 v17
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v18 v19
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v20 v21 v22
                      -> case coe v21 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v23 v24
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_effApp_72 v11 v12 v9 v14
                                  (d_realize'45'infer_34
                                     (coe v0) (coe v1) (coe v18)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v9)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v24))
                                        (coe v22))
                                     (coe v11) (coe v16))
                                  (d_realize_22
                                     (coe v0) (coe v1) (coe v19) (coe v9) (coe v12) (coe v17))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'app'45'spine_424 v9 v11 v12 v14 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v16 v17
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_app_54 v11 v12 v9
                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                    (d_realize'45'd_50
                       (coe v0) (coe v1) (coe v16) (coe v9) (coe v3)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_fin_42
                          (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
                       (coe v11) (coe v15))
                    (d_realize'45'infer_34
                       (coe v0) (coe v1) (coe v17) (coe v9) (coe v12) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Realize.realize-d
d_realize'45'd_50 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_realize'45'd_50 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.Internal.Typing.C_d'45'infer_796 v11 v14 v16 v17 v18
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
             (coe
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v11)
                (coe
                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v14))
                (coe v4))
             (coe
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40 v17
                (coe
                   MAlonzo.Code.Once.Internal.Type.Sub.du_'60''58''45'refl_62
                   (coe v4))
                v18)
             (d_realize'45'infer_34
                (coe v0) (coe v1) (coe v2)
                (coe
                   MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v11)
                   (coe
                      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v14))
                   (coe v4))
                (coe v6) (coe v16))
      MAlonzo.Code.Once.Internal.Typing.C_d'45'poly_820 v13 v14 v15 v16 v17 v18 v23 v24 v25 v26
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v27
               -> case coe v27 of
                    MAlonzo.Code.Once.Spec.Name.C_canonical_12 v28
                      -> case coe v28 of
                           (:) v29 v30
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                                  (coe
                                     MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v3)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))
                                     (coe v4))
                                  (coe
                                     MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40
                                     (coe
                                        MAlonzo.Code.Once.Internal.Type.Sub.du_'60''58''45'refl_62
                                        (coe v3))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Type.Sub.du_'60''58''45'refl_62
                                        (coe v4))
                                     v26)
                                  (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_406 v29)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_d'45'lam_840 v13 v16 v17
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 v18 v19
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_38 v13
                    (d_realize'45'infer_34
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Internal.Typing.Scope.C_mkCtx_146
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v1)))
                          (coe
                             MAlonzo.Code.Once.Internal.Typing.Scope.du_extendCtx_34
                             (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_named_134 (coe v1))
                             (coe v18) (coe v3))
                          (coe
                             MAlonzo.Code.Once.Spec.Context.C__'9656'__16
                             (MAlonzo.Code.Once.Internal.Typing.Scope.d_debruijn_136 (coe v1))
                             v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Typing.Scope.d_imports_138 (coe v1))
                          (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_polys_140 (coe v1))
                          (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_sig_142 (coe v1))
                          (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_kinds_144 (coe v1)))
                       (coe v19) (coe v4)
                       (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v13 v6)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_d'45'compose_860 v12 v15 v16 v17 v18
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v21 v22
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_comp''_456 v15 v16 v12
                           (d_realize'45'd_50
                              (coe v0) (coe v1) (coe v22) (coe v12) (coe v4) (coe v5) (coe v15)
                              (coe v18))
                           (d_realize'45'd_50
                              (coe v0) (coe v1) (coe v20) (coe v3) (coe v12) (coe v5) (coe v16)
                              (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_d'45'id_870 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_id_20)
      MAlonzo.Code.Once.Internal.Typing.C_d'45'fst_882 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_fst_42)
      MAlonzo.Code.Once.Internal.Typing.C_d'45'snd_894 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_snd_48)
      MAlonzo.Code.Once.Internal.Typing.C_d'45'terminal_904 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_terminal_72)
      MAlonzo.Code.Once.Internal.Typing.C_d'45'initial_912 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_initial_76)
      MAlonzo.Code.Once.Internal.Typing.C_d'45'case_936 v13 v14 v17 v18 v19 v20 v21
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v22 v23
               -> case coe v22 of
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v24 v25
                      -> case coe v3 of
                           MAlonzo.Code.Once.Spec.Type.C__'43'__24 v26 v27
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_copair''_474 v17 v18
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v26)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v5))
                                        (coe v13))
                                     (coe
                                        MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40
                                        (coe
                                           MAlonzo.Code.Once.Internal.Type.Sub.du_'60''58''45'refl_62
                                           (coe v26))
                                        (coe
                                           MAlonzo.Code.Once.Internal.Type.Sub.du_'60''58''7580''8658''60''58'_92
                                           (coe v13) (coe v4)
                                           (coe MAlonzo.Code.Once.Spec.Sub.d_left_166 (coe v21)))
                                        (MAlonzo.Code.Once.Internal.Type.Sub.d_'8849'π'45'refl_42
                                           (coe v5)))
                                     (d_realize'45'd_50
                                        (coe v0) (coe v1) (coe v25) (coe v26) (coe v13) (coe v5)
                                        (coe v17) (coe v19)))
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v27)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v5))
                                        (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40
                                        (coe
                                           MAlonzo.Code.Once.Internal.Type.Sub.du_'60''58''45'refl_62
                                           (coe v27))
                                        (coe
                                           MAlonzo.Code.Once.Internal.Type.Sub.du_'60''58''7580''8658''60''58'_92
                                           (coe v14) (coe v4)
                                           (coe MAlonzo.Code.Once.Spec.Sub.d_right_168 (coe v21)))
                                        (MAlonzo.Code.Once.Internal.Type.Sub.d_'8849'π'45'refl_42
                                           (coe v5)))
                                     (d_realize'45'd_50
                                        (coe v0) (coe v1) (coe v23) (coe v27) (coe v14) (coe v5)
                                        (coe v18) (coe v20)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_d'45'pair_956 v15 v16 v17 v18
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v21 v22
                      -> case coe v4 of
                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 v23 v24
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_fork''_492 v15 v16
                                  (d_realize'45'd_50
                                     (coe v0) (coe v1) (coe v22) (coe v3) (coe v23) (coe v5)
                                     (coe v15) (coe v17))
                                  (d_realize'45'd_50
                                     (coe v0) (coe v1) (coe v20) (coe v3) (coe v24) (coe v5)
                                     (coe v16) (coe v18))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_d'45'cata_972 v13 v14 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v17 v18
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Type.C_μ_28 v19
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_cata_526 v13
                           (MAlonzo.Code.Once.Internal.Typing.Scope.d_kinds_144 (coe v1)) v15
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v18)
                              (coe
                                 MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                 (coe
                                    MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v19)
                                    (coe v4))
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v5))
                                 (coe v4))
                              (coe v13) (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
