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
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v5 v7 v8
           -> coe du_pureArrow_8 (coe v5)
         _ -> coe v1)
-- Once.Surface.LoopWarn.silentLoops
d_silentLoops_34 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> Integer
d_silentLoops_34 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_silentLoops_34 v4 v5
du_silentLoops_34 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> Integer
du_silentLoops_34 v0 v1
  = let v2 = 0 :: Integer in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Surface.Syntax.C_lam_38 v6 v12
           -> case coe v0 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v13 v14 v15
                  -> coe du_silentLoops_34 (coe v15) (coe v12)
                _ -> coe v2
         MAlonzo.Code.Once.Surface.Syntax.C_app_54 v5 v6 v7 v9 v10 v11
           -> coe
                addInt
                (coe
                   du_silentLoops_34
                   (coe
                      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v7)
                      (coe
                         MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v9)
                         (coe
                            MAlonzo.Code.Once.Spec.Grade.C_fin_42
                            (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                      (coe v0))
                   (coe v10))
                (coe du_silentLoops_34 (coe v7) (coe v11))
         MAlonzo.Code.Once.Surface.Syntax.C_effApp_72 v5 v6 v7 v10 v11 v12
           -> case coe v0 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v13 v14 v15
                  -> case coe v14 of
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v16 v17
                         -> coe
                              addInt
                              (coe
                                 du_silentLoops_34
                                 (coe
                                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v7)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v17))
                                    (coe v15))
                                 (coe v11))
                              (coe du_silentLoops_34 (coe v7) (coe v12))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v2
         MAlonzo.Code.Once.Surface.Syntax.C_pair_86 v5 v6 v9 v10
           -> case coe v0 of
                MAlonzo.Code.Once.Spec.Type.C__'42'__22 v11 v12
                  -> coe
                       addInt (coe du_silentLoops_34 (coe v11) (coe v9))
                       (coe du_silentLoops_34 (coe v12) (coe v10))
                _ -> coe v2
         MAlonzo.Code.Once.Surface.Syntax.C_fst''_98 v7 v8
           -> coe
                du_silentLoops_34
                (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v0) (coe v7))
                (coe v8)
         MAlonzo.Code.Once.Surface.Syntax.C_snd''_110 v6 v8
           -> coe
                du_silentLoops_34
                (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v6) (coe v0))
                (coe v8)
         MAlonzo.Code.Once.Surface.Syntax.C_inl''_122 v8
           -> case coe v0 of
                MAlonzo.Code.Once.Spec.Type.C__'43'__24 v9 v10
                  -> coe du_silentLoops_34 (coe v9) (coe v8)
                _ -> coe v2
         MAlonzo.Code.Once.Surface.Syntax.C_inr''_134 v8
           -> case coe v0 of
                MAlonzo.Code.Once.Spec.Type.C__'43'__24 v9 v10
                  -> coe du_silentLoops_34 (coe v10) (coe v8)
                _ -> coe v2
         MAlonzo.Code.Once.Surface.Syntax.C_case''_156 v5 v6 v7 v8 v9 v10 v11 v13 v14 v15
           -> coe
                addInt
                (coe
                   addInt
                   (coe
                      du_silentLoops_34
                      (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v10) (coe v11))
                      (coe v13))
                   (coe du_silentLoops_34 (coe v0) (coe v14)))
                (coe du_silentLoops_34 (coe v0) (coe v15))
         MAlonzo.Code.Once.Surface.Syntax.C_absurd_172 v7
           -> coe
                du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
                (coe v7)
         MAlonzo.Code.Once.Surface.Syntax.C_let''_188 v5 v6 v7 v8 v10 v11
           -> coe
                addInt (coe du_silentLoops_34 (coe v0) (coe v11))
                (coe du_silentLoops_34 (coe v8) (coe v10))
         MAlonzo.Code.Once.Surface.Syntax.C_add_212 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                   (coe v7))
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_sub_222 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                   (coe v7))
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_mul_232 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                   (coe v7))
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_fadd_242 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
                   (coe v7))
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_fsub_252 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
                   (coe v7))
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_fmul_262 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
                   (coe v7))
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_fdiv_272 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
                   (coe v7))
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_i2f_280 v6
           -> coe
                du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                (coe v6)
         MAlonzo.Code.Once.Surface.Syntax.C_div_290 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                   (coe v7))
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_mod''_300 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                   (coe v7))
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_neg_308 v6
           -> coe
                du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                (coe v6)
         MAlonzo.Code.Once.Surface.Syntax.C_lt_318 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                   (coe v7))
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_le_328 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                   (coe v7))
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_gt_338 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                   (coe v7))
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_ge_348 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                   (coe v7))
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_eq_358 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                   (coe v7))
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_ne_368 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                   (coe v7))
                (coe
                   du_silentLoops_34 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v6 v8 v9
           -> coe du_silentLoops_34 (coe v6) (coe v9)
         MAlonzo.Code.Once.Surface.Syntax.C_closed_414 v6
           -> coe du_silentLoops_34 (coe v0) (coe v6)
         MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v5 v6 v8 v9
           -> coe du_silentLoops_34 (coe v6) (coe v9)
         MAlonzo.Code.Once.Surface.Syntax.C_comp''_456 v5 v6 v8 v11 v12
           -> case coe v0 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v13 v14 v15
                  -> case coe v14 of
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v16 v17
                         -> coe
                              addInt
                              (coe
                                 du_silentLoops_34
                                 (coe
                                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v8)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v17))
                                    (coe v15))
                                 (coe v11))
                              (coe
                                 du_silentLoops_34
                                 (coe
                                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v13)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v17))
                                    (coe v8))
                                 (coe v12))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v2
         MAlonzo.Code.Once.Surface.Syntax.C_copair''_474 v5 v6 v11 v12
           -> case coe v0 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v13 v14 v15
                  -> case coe v13 of
                       MAlonzo.Code.Once.Spec.Type.C__'43'__24 v16 v17
                         -> case coe v14 of
                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v18 v19
                                -> coe
                                     addInt
                                     (coe
                                        du_silentLoops_34
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                           (coe v16)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                              (coe v19))
                                           (coe v15))
                                        (coe v11))
                                     (coe
                                        du_silentLoops_34
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                           (coe v17)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                              (coe v19))
                                           (coe v15))
                                        (coe v12))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v2
                _ -> coe v2
         MAlonzo.Code.Once.Surface.Syntax.C_fork''_492 v5 v6 v11 v12
           -> case coe v0 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v13 v14 v15
                  -> case coe v14 of
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v16 v17
                         -> case coe v15 of
                              MAlonzo.Code.Once.Spec.Type.C__'42'__22 v18 v19
                                -> coe
                                     addInt
                                     (coe
                                        du_silentLoops_34
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                           (coe v13)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                              (coe v17))
                                           (coe v18))
                                        (coe v11))
                                     (coe
                                        du_silentLoops_34
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                           (coe v13)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                              (coe v17))
                                           (coe v19))
                                        (coe v12))
                              _ -> coe v2
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v2
         MAlonzo.Code.Once.Surface.Syntax.C_curry''_510 v11
           -> case coe v0 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v12 v13 v14
                  -> case coe v14 of
                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v15 v16 v17
                         -> case coe v16 of
                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v18 v19
                                -> coe
                                     du_silentLoops_34
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v12)
                                           (coe v15))
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v19))
                                        (coe v17))
                                     (coe v11)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v2
                _ -> coe v2
         MAlonzo.Code.Once.Surface.Syntax.C_cata_526 v5 v7 v10 v11
           -> case coe v0 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v12 v13 v14
                  -> case coe v12 of
                       MAlonzo.Code.Once.Spec.Type.C_μ_28 v15
                         -> case coe v13 of
                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v16 v17
                                -> coe
                                     du_silentLoops_34
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50
                                           (coe v15) (coe v14))
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v17))
                                        (coe v14))
                                     (coe v11)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v2
                _ -> coe v2
         MAlonzo.Code.Once.Surface.Syntax.C_ana_544 v5 v7 v11 v12
           -> case coe v0 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v13 v14 v15
                  -> case coe v15 of
                       MAlonzo.Code.Once.Spec.Type.C_ν_30 v16 v17
                         -> coe
                              du_silentLoops_34
                              (coe
                                 MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v17)))
                                 (coe
                                    MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v16)
                                    (coe v13)))
                              (coe v12)
                       _ -> coe v2
                _ -> coe v2
         MAlonzo.Code.Once.Surface.Syntax.C_loop_556 v5 v8
           -> case coe v0 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v9 v10 v11
                  -> coe
                       addInt
                       (coe
                          MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                          (coe du_roundIsPure_20 (coe v8)) (coe (1 :: Integer))
                          (coe (0 :: Integer)))
                       (coe
                          du_silentLoops_34
                          (coe
                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v9)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                (coe
                                   MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                   (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
                             (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v11) (coe v9)))
                          (coe v8))
                _ -> coe v2
         _ -> coe v2)
