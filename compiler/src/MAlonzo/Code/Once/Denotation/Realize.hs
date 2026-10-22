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
import qualified MAlonzo.Code.Once.Internal.Syntax
import qualified MAlonzo.Code.Once.Internal.Type.Sub
import qualified MAlonzo.Code.Once.Internal.Typing
import qualified MAlonzo.Code.Once.Internal.Typing.Scope
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Sub
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
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__20 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_realize_22 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Internal.Typing.C_t'45'id'45'check_450 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_id_20)
      MAlonzo.Code.Once.Internal.Typing.C_t'45'fst'45'check_462 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_fst_42)
      MAlonzo.Code.Once.Internal.Typing.C_t'45'snd'45'check_474 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_snd_48)
      MAlonzo.Code.Once.Internal.Typing.C_t'45'terminal'45'morph'45'check_484 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_terminal_72)
      MAlonzo.Code.Once.Internal.Typing.C_t'45'initial'45'morph'45'check_494 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_initial_76)
      MAlonzo.Code.Once.Internal.Typing.C_t'45'inl'45'morph'45'check_506 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_inl_54)
      MAlonzo.Code.Once.Internal.Typing.C_t'45'inr'45'morph'45'check_518 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_inr_60)
      MAlonzo.Code.Once.Internal.Typing.C_t'45'compose'45'check'45'g_538 v10 v13 v14 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v19 v20
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'compose'45'check'45'f_562 v10 v12 v14 v15 v16 v17 v18 v19
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v20 v21
               -> case coe v20 of
                    MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v22 v23
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'case'45'copair'45'check_582 v13 v14 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v19 v20
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'pair'45'morph'45'check_602 v13 v14 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v19 v20
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'curry'45'check_622 v14 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v16 v17
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'cata'45'check_638 v11 v12 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v15 v16
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'ana'45'check_658 v12 v13 v14 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v17 v18
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'loop'45'check_670 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v12 v13
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'sub_682 v8 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v8 v12
             (d_realize'45'infer_34
                (coe v0) (coe v1) (coe v2) (coe v8) (coe v4) (coe v11))
      MAlonzo.Code.Once.Internal.Typing.C_t'45'lam_704 v12 v15 v17
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RLam_44 v18 v19
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'pair'45'lit'45'check_720 v11 v12 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RPair_48 v15 v16
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'In'45'app'45'check_730 v9 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v12 v13
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'apply'45'check_742 v8 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v12 v13
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'inl'45'app'45'check_754 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v12 v13
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v10 v14
                           (coe MAlonzo.Code.Once.IR.C_inl_54)
                           (d_realize_22
                              (coe v0) (coe v1) (coe v13) (coe v14) (coe v10) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'inr'45'app'45'check_766 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v12 v13
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v10 v15
                           (coe MAlonzo.Code.Once.IR.C_inr_60)
                           (d_realize_22
                              (coe v0) (coe v1) (coe v13) (coe v15) (coe v10) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'initial'45'app'45'check_776 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v9
                    (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
                    (coe MAlonzo.Code.Once.IR.C_initial_76)
                    (d_realize_22
                       (coe v0) (coe v1) (coe v12)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Void_20) (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'poly'45'instantiate_790 v9 v10 v11 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RResolved_40 v17
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
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_realize'45'infer_34 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Internal.Typing.C_t'45'int_38
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RInt_54 v8
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_int_194 v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'float_50
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RFloat_56 v11 v12 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_float_202
                    (MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30
                       (coe v11) (coe v12) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'unit_54
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_162
      MAlonzo.Code.Once.Internal.Typing.C_t'45'unit'45'var_58
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_162
      MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'local_70 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.du_svar'8594'expr_568 (coe v10)
      MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'resolved_80 v8 v10 v11 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RResolved_40 v15
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_388 v8 v15 v13
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'own_90 v8
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RResolved_40 v13
               -> case coe v13 of
                    MAlonzo.Code.Once.Spec.Name.C_canonical_12 v14
                      -> case coe v14 of
                           (:) v15 v16
                             -> coe MAlonzo.Code.Once.Surface.Syntax.C_closure_396 v15
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'import_100 v8 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RVar_36 v15
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_closure_396 v15
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'poly'45'instantiate'45'infer_116 v9 v10 v11 v12 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RResolved_40 v18
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Name.C_canonical_12 v19
                      -> case coe v19 of
                           (:) v20 v21 -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_406 v20
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'annot_128 v11 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RAnnot_58 v14 v15
               -> coe
                    d_realize_22 (coe v0) (coe v1) (coe v14) (coe v3) (coe v4)
                    (coe v12)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'pair_144 v11 v12 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RPair_48 v15 v16
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'neg_152 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RUnaryOp_62 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_neg_308
                    (d_realize'45'infer_34
                       (coe v0) (coe v1) (coe v11)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v4) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'neg'45'float_164
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RUnaryOp_62 v12
               -> case coe v12 of
                    MAlonzo.Code.Once.Internal.Syntax.C_RFloat_56 v13 v14 v15 v16
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_float_202
                           (MAlonzo.Code.Once.Spec.Float.Decimal.d_negate_24
                              (coe
                                 MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30 (coe v13)
                                 (coe v14) (coe v15)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'let_184 v10 v12 v13 v14 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RLet_46 v17 v18 v19
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'case_218 v12 v13 v14 v15 v17 v18 v19 v20 v21 v22 v23 v24 v25
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RDestruct_50 v26 v27 v28 v29 v30
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith_232 v10 v11 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_60 v15 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Internal.Syntax.C_OpAdd_8
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_add_212 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Internal.Syntax.C_OpSub_10
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_sub_222 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Internal.Syntax.C_OpMul_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_mul_232 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Internal.Syntax.C_OpDiv_14
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_div_290 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Internal.Syntax.C_OpMod_16
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float_246 v10 v11 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_60 v15 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Internal.Syntax.C_OpAdd_8
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fadd_242 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Internal.Syntax.C_OpSub_10
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fsub_252 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Internal.Syntax.C_OpMul_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fmul_262 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Internal.Syntax.C_OpDiv_14
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'il_260 v10 v11 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_60 v15 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Internal.Syntax.C_OpAdd_8
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
                    MAlonzo.Code.Once.Internal.Syntax.C_OpSub_10
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
                    MAlonzo.Code.Once.Internal.Syntax.C_OpMul_12
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
                    MAlonzo.Code.Once.Internal.Syntax.C_OpDiv_14
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'ir_274 v10 v11 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_60 v15 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Internal.Syntax.C_OpAdd_8
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
                    MAlonzo.Code.Once.Internal.Syntax.C_OpSub_10
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
                    MAlonzo.Code.Once.Internal.Syntax.C_OpMul_12
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
                    MAlonzo.Code.Once.Internal.Syntax.C_OpDiv_14
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'cmp_288 v10 v11 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_60 v15 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Internal.Syntax.C_OpLt_18
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_lt_318 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Internal.Syntax.C_OpLe_20
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_le_328 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Internal.Syntax.C_OpGt_22
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_gt_338 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Internal.Syntax.C_OpGe_24
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_ge_348 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Internal.Syntax.C_OpEq_26
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_eq_358 v10 v11
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v16)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v10) (coe v13))
                           (d_realize'45'infer_34
                              (coe v0) (coe v1) (coe v17)
                              (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v11) (coe v14))
                    MAlonzo.Code.Once.Internal.Syntax.C_OpNe_28
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'id'45'app_298 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v9 v3
                    (coe MAlonzo.Code.Once.IR.C_id_20)
                    (d_realize'45'infer_34
                       (coe v0) (coe v1) (coe v12) (coe v3) (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'fst'45'app_310 v9 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v10
                    (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v3) (coe v9))
                    (coe MAlonzo.Code.Once.IR.C_fst_42)
                    (d_realize'45'infer_34
                       (coe v0) (coe v1) (coe v13)
                       (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v3) (coe v9))
                       (coe v10) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'snd'45'app_322 v8 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v10
                    (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v8) (coe v3))
                    (coe MAlonzo.Code.Once.IR.C_snd_48)
                    (d_realize'45'infer_34
                       (coe v0) (coe v1) (coe v13)
                       (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v8) (coe v3))
                       (coe v10) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'terminal'45'app_332 v8 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v9 v8
                    (coe MAlonzo.Code.Once.IR.C_terminal_72)
                    (d_realize'45'infer_34
                       (coe v0) (coe v1) (coe v12) (coe v8) (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.C_t'45'apply'45'app'45'infer_344 v8 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v12 v13
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'apply'45'eff'45'app'45'infer_360 v8 v10 v12 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v14 v15
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'Out'45'app'45'infer_372 v8 v10 v11 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v14 v15
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'Out'45'eff'45'app'45'infer_384 v8 v10 v11 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v14 v15
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'app_402 v9 v11 v12 v13 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v17 v18
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'effApp_422 v9 v11 v12 v14 v16 v17
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v18 v19
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
      MAlonzo.Code.Once.Internal.Typing.C_t'45'app'45'spine_438 v9 v11 v12 v14 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v16 v17
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
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__30 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_realize'45'd_50 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.Internal.Typing.C_d'45'infer_810 v11 v14 v16 v17 v18
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
      MAlonzo.Code.Once.Internal.Typing.C_d'45'poly_834 v13 v14 v15 v16 v17 v18 v23 v24 v25 v26
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RResolved_40 v27
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
      MAlonzo.Code.Once.Internal.Typing.C_d'45'lam_854 v13 v16 v17
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RLam_44 v18 v19
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
      MAlonzo.Code.Once.Internal.Typing.C_d'45'compose_874 v12 v15 v16 v17 v18
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v21 v22
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
      MAlonzo.Code.Once.Internal.Typing.C_d'45'id_884 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_id_20)
      MAlonzo.Code.Once.Internal.Typing.C_d'45'fst_896 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_fst_42)
      MAlonzo.Code.Once.Internal.Typing.C_d'45'snd_908 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_snd_48)
      MAlonzo.Code.Once.Internal.Typing.C_d'45'terminal_918 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_terminal_72)
      MAlonzo.Code.Once.Internal.Typing.C_d'45'initial_926 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
             (coe MAlonzo.Code.Once.IR.C_initial_76)
      MAlonzo.Code.Once.Internal.Typing.C_d'45'case_950 v13 v14 v17 v18 v19 v20 v21
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v22 v23
               -> case coe v22 of
                    MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v24 v25
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
      MAlonzo.Code.Once.Internal.Typing.C_d'45'pair_970 v15 v16 v17 v18
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v21 v22
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
      MAlonzo.Code.Once.Internal.Typing.C_d'45'cata_986 v13 v14 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v17 v18
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
