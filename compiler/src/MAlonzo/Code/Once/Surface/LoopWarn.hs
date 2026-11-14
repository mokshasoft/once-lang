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

module MAlonzo.Code.Once.Surface.LoopWarn where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Theory
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Surface.Syntax

-- Once.Surface.LoopWarn.pureArrow
d_pureArrow_8 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Bool
d_pureArrow_8 ~v0 v1 = du_pureArrow_8 v1
du_pureArrow_8 :: MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Bool
du_pureArrow_8 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v5 v6
                  -> case coe v6 of
                       MAlonzo.Code.Once.Spec.Grade.C_fin_42 v7
                         -> case coe v7 of
                              MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                              _ -> coe v1
                       _ -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.Surface.LoopWarn.roundIsPure
d_roundIsPure_20 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> Bool
d_roundIsPure_20 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_roundIsPure_20 v5
du_roundIsPure_20 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> Bool
du_roundIsPure_20 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_228 v5 v7 v8
           -> coe du_pureArrow_8 (coe v5)
         _ -> coe v1)
-- Once.Surface.LoopWarn.Here
d_Here_24 :: ()
d_Here_24 = erased
-- Once.Surface.LoopWarn.exprCount
d_exprCount_46 ::
  (Integer ->
   Integer ->
   MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
   MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> Integer
d_exprCount_46 v0 v1 v2 v3 v4 v5 v6
  = coe
      addInt
      (coe
         du_below_66 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
      (coe v0 v1 v2 v3 v4 v5 v6)
-- Once.Surface.LoopWarn._.below
d_below_66 ::
  (Integer ->
   Integer ->
   MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
   MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> Integer
d_below_66 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10 v11 v12
  = du_below_66 v0 v7 v8 v9 v10 v11 v12
du_below_66 ::
  (Integer ->
   Integer ->
   MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
   MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> Integer
du_below_66 v0 v1 v2 v3 v4 v5 v6
  = let v7 = 0 :: Integer in
    coe
      (case coe v6 of
         MAlonzo.Code.Once.Surface.Syntax.C_lam_38 v11 v17
           -> case coe v5 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v18 v19 v20
                  -> coe
                       d_exprCount_46 (coe v0) (coe v1)
                       (coe addInt (coe (1 :: Integer)) (coe v2))
                       (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v3 v18)
                       (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v11 v4) (coe v20)
                       (coe v17)
                _ -> coe v7
         MAlonzo.Code.Once.Surface.Syntax.C_app_54 v10 v11 v12 v14 v15 v16
           -> coe
                addInt
                (coe
                   d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                   (coe
                      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v12)
                      (coe
                         MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v14)
                         (coe
                            MAlonzo.Code.Once.Spec.Grade.C_fin_42
                            (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                      (coe v5))
                   (coe v15))
                (coe
                   d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v11)
                   (coe v12) (coe v16))
         MAlonzo.Code.Once.Surface.Syntax.C_effApp_72 v10 v11 v12 v15 v16 v17
           -> case coe v5 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v18 v19 v20
                  -> case coe v19 of
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v21 v22
                         -> coe
                              addInt
                              (coe
                                 d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v12)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v22))
                                    (coe v20))
                                 (coe v16))
                              (coe
                                 d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v11)
                                 (coe v12) (coe v17))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v7
         MAlonzo.Code.Once.Surface.Syntax.C_pair_86 v10 v11 v14 v15
           -> case coe v5 of
                MAlonzo.Code.Once.Spec.Type.C__'42'__22 v16 v17
                  -> coe
                       addInt
                       (coe
                          d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                          (coe v16) (coe v14))
                       (coe
                          d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v11)
                          (coe v17) (coe v15))
                _ -> coe v7
         MAlonzo.Code.Once.Surface.Syntax.C_fst''_98 v12 v13
           -> coe
                d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v5) (coe v12))
                (coe v13)
         MAlonzo.Code.Once.Surface.Syntax.C_snd''_110 v11 v13
           -> coe
                d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v11) (coe v5))
                (coe v13)
         MAlonzo.Code.Once.Surface.Syntax.C_inl''_122 v13
           -> case coe v5 of
                MAlonzo.Code.Once.Spec.Type.C__'43'__24 v14 v15
                  -> coe
                       d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v14) (coe v13)
                _ -> coe v7
         MAlonzo.Code.Once.Surface.Syntax.C_inr''_134 v13
           -> case coe v5 of
                MAlonzo.Code.Once.Spec.Type.C__'43'__24 v14 v15
                  -> coe
                       d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v15) (coe v13)
                _ -> coe v7
         MAlonzo.Code.Once.Surface.Syntax.C_case''_156 v10 v11 v12 v13 v14 v15 v16 v18 v19 v20
           -> coe
                addInt
                (coe
                   addInt
                   (coe
                      d_exprCount_46 (coe v0) (coe v1)
                      (coe addInt (coe (1 :: Integer)) (coe v2))
                      (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v3 v15)
                      (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v13 v11) (coe v5)
                      (coe v19))
                   (coe
                      d_exprCount_46 (coe v0) (coe v1)
                      (coe addInt (coe (1 :: Integer)) (coe v2))
                      (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v3 v16)
                      (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v14 v12) (coe v5)
                      (coe v20)))
                (coe
                   d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                   (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v15) (coe v16))
                   (coe v18))
         MAlonzo.Code.Once.Surface.Syntax.C_absurd_172 v12
           -> coe
                d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe MAlonzo.Code.Once.Spec.Type.C_Void_20) (coe v12)
         MAlonzo.Code.Once.Surface.Syntax.C_let''_188 v10 v11 v12 v13 v15 v16
           -> coe
                addInt
                (coe
                   d_exprCount_46 (coe v0) (coe v1)
                   (coe addInt (coe (1 :: Integer)) (coe v2))
                   (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v3 v13)
                   (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v12 v11) (coe v5)
                   (coe v16))
                (coe
                   d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                   (coe v13) (coe v15))
         MAlonzo.Code.Once.Surface.Syntax.C_num_216 v11 v12 v13 v14 v15 v16
           -> coe
                d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe
                   MAlonzo.Code.Once.Spec.Theory.du_symDom_86 (coe v11) (coe v13))
                (coe v16)
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_228 v11 v13 v14
           -> coe
                d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v11) (coe v14)
         MAlonzo.Code.Once.Surface.Syntax.C_closed_262 v11
           -> coe
                d_exprCount_46 (coe v0) (coe v1) (coe (0 :: Integer))
                (coe MAlonzo.Code.Once.Spec.Context.C_'8709'_12)
                (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36) (coe v5)
                (coe v11)
         MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_286 v10 v11 v13 v14
           -> coe
                d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                (coe v11) (coe v14)
         MAlonzo.Code.Once.Surface.Syntax.C_comp''_304 v10 v11 v13 v16 v17
           -> case coe v5 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v18 v19 v20
                  -> case coe v19 of
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v21 v22
                         -> coe
                              addInt
                              (coe
                                 d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v13)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v22))
                                    (coe v20))
                                 (coe v16))
                              (coe
                                 d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v11)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v18)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v22))
                                    (coe v13))
                                 (coe v17))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v7
         MAlonzo.Code.Once.Surface.Syntax.C_copair''_322 v10 v11 v16 v17
           -> case coe v5 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v18 v19 v20
                  -> case coe v18 of
                       MAlonzo.Code.Once.Spec.Type.C__'43'__24 v21 v22
                         -> case coe v19 of
                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v23 v24
                                -> coe
                                     addInt
                                     (coe
                                        d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                           (coe v21)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                              (coe v24))
                                           (coe v20))
                                        (coe v16))
                                     (coe
                                        d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v11)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                           (coe v22)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                              (coe v24))
                                           (coe v20))
                                        (coe v17))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v7
                _ -> coe v7
         MAlonzo.Code.Once.Surface.Syntax.C_fork''_340 v10 v11 v16 v17
           -> case coe v5 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v18 v19 v20
                  -> case coe v19 of
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v21 v22
                         -> case coe v20 of
                              MAlonzo.Code.Once.Spec.Type.C__'42'__22 v23 v24
                                -> coe
                                     addInt
                                     (coe
                                        d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                           (coe v18)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                              (coe v22))
                                           (coe v23))
                                        (coe v16))
                                     (coe
                                        d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v11)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                           (coe v18)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                              (coe v22))
                                           (coe v24))
                                        (coe v17))
                              _ -> coe v7
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v7
         MAlonzo.Code.Once.Surface.Syntax.C_curry''_358 v16
           -> case coe v5 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
                  -> case coe v19 of
                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v20 v21 v22
                         -> case coe v21 of
                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v23 v24
                                -> coe
                                     d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v17)
                                           (coe v20))
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v24))
                                        (coe v22))
                                     (coe v16)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v7
                _ -> coe v7
         MAlonzo.Code.Once.Surface.Syntax.C_cata_374 v10 v12 v15 v16
           -> case coe v5 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
                  -> case coe v17 of
                       MAlonzo.Code.Once.Spec.Type.C_μ_28 v20
                         -> case coe v18 of
                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v21 v22
                                -> coe
                                     d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50
                                           (coe v20) (coe v19))
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v22))
                                        (coe v19))
                                     (coe v16)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v7
                _ -> coe v7
         MAlonzo.Code.Once.Surface.Syntax.C_ana_392 v10 v12 v16 v17
           -> case coe v5 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v18 v19 v20
                  -> case coe v20 of
                       MAlonzo.Code.Once.Spec.Type.C_ν_30 v21 v22
                         -> coe
                              d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                              (coe
                                 MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v18)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v22)))
                                 (coe
                                    MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v21)
                                    (coe v18)))
                              (coe v17)
                       _ -> coe v7
                _ -> coe v7
         MAlonzo.Code.Once.Surface.Syntax.C_loop_404 v10 v13
           -> case coe v5 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v14 v15 v16
                  -> coe
                       d_exprCount_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                       (coe
                          MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v14)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
                          (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v16) (coe v14)))
                       (coe v13)
                _ -> coe v7
         _ -> coe v7)
-- Once.Surface.LoopWarn.silentLoops
d_silentLoops_130 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> Integer
d_silentLoops_130 v0 v1 v2 v3 v4
  = coe
      d_exprCount_46 (\ v5 v6 v7 v8 v9 v10 -> coe du_here_136 v9 v10)
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.Surface.LoopWarn._.here
d_here_136 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> Integer
d_here_136 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_here_136 v9 v10
du_here_136 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> Integer
du_here_136 v0 v1
  = let v2 = 0 :: Integer in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Surface.Syntax.C_loop_404 v5 v8
           -> case coe v0 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v9 v10 v11
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe du_roundIsPure_20 (coe v8)) (coe (1 :: Integer))
                       (coe (0 :: Integer))
                _ -> coe v2
         _ -> coe v2)
-- Once.Surface.LoopWarn.floatIdentityEqs
d_floatIdentityEqs_140 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> Integer
d_floatIdentityEqs_140 v0 v1 v2 v3 v4
  = coe
      d_exprCount_46 (\ v5 v6 v7 v8 v9 v10 -> coe du_here_146 v10)
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.Surface.LoopWarn._.here
d_here_146 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> Integer
d_here_146 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_here_146 v10
du_here_146 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> Integer
du_here_146 v0
  = let v1 = 0 :: Integer in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Surface.Syntax.C_num_216 v5 v6 v7 v8 v9 v10
           -> case coe v8 of
                MAlonzo.Code.Once.Spec.Theory.C_float'45'equality_122
                  -> case coe v9 of
                       MAlonzo.Code.Once.Spec.Theory.C_'8245''61''61'_60
                         -> coe (1 :: Integer)
                       MAlonzo.Code.Once.Spec.Theory.C_'8245''33''61'_62
                         -> coe (1 :: Integer)
                       _ -> coe v1
                _ -> coe v1
         _ -> coe v1)
