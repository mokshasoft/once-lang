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
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Surface.Syntax

-- Once.Surface.LoopWarn.pureArrow
d_pureArrow_6 :: MAlonzo.Code.Once.Lang.Type.T_Type_8 -> Bool
d_pureArrow_6 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v5 v6
                  -> case coe v6 of
                       MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
                         -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                       _ -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.Surface.LoopWarn.roundIsPure
d_roundIsPure_16 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> Bool
d_roundIsPure_16 ~v0 ~v1 ~v2 ~v3 v4 = du_roundIsPure_16 v4
du_roundIsPure_16 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> Bool
du_roundIsPure_16 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v5 v7 v8
           -> coe d_pureArrow_6 (coe v5)
         _ -> coe v1)
-- Once.Surface.LoopWarn.silentLoops
d_silentLoops_28 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> Integer
d_silentLoops_28 ~v0 ~v1 ~v2 v3 v4 = du_silentLoops_28 v3 v4
du_silentLoops_28 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> Integer
du_silentLoops_28 v0 v1
  = let v2 = 0 :: Integer in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v6 v12
           -> case coe v0 of
                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v13 v14 v15
                  -> coe du_silentLoops_28 (coe v15) (coe v12)
                _ -> coe v2
         MAlonzo.Code.Once.Surface.Syntax.C_app_50 v5 v6 v7 v9 v10 v11
           -> coe
                addInt
                (coe
                   du_silentLoops_28
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 (coe v9)
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                      (coe v0))
                   (coe v10))
                (coe du_silentLoops_28 (coe v7) (coe v11))
         MAlonzo.Code.Once.Surface.Syntax.C_effApp_68 v5 v6 v7 v10 v11 v12
           -> case coe v0 of
                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v13 v14 v15
                  -> case coe v14 of
                       MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v16 v17
                         -> coe
                              addInt
                              (coe
                                 du_silentLoops_28
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v17))
                                    (coe v15))
                                 (coe v11))
                              (coe du_silentLoops_28 (coe v7) (coe v12))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v2
         MAlonzo.Code.Once.Surface.Syntax.C_pair_82 v5 v6 v9 v10
           -> case coe v0 of
                MAlonzo.Code.Once.Lang.Type.C__'42'__24 v11 v12
                  -> coe
                       addInt (coe du_silentLoops_28 (coe v11) (coe v9))
                       (coe du_silentLoops_28 (coe v12) (coe v10))
                _ -> coe v2
         MAlonzo.Code.Once.Surface.Syntax.C_fst''_94 v7 v8
           -> coe
                du_silentLoops_28
                (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v0) (coe v7))
                (coe v8)
         MAlonzo.Code.Once.Surface.Syntax.C_snd''_106 v6 v8
           -> coe
                du_silentLoops_28
                (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v6) (coe v0))
                (coe v8)
         MAlonzo.Code.Once.Surface.Syntax.C_inl''_118 v8
           -> case coe v0 of
                MAlonzo.Code.Once.Lang.Type.C__'43'__26 v9 v10
                  -> coe du_silentLoops_28 (coe v9) (coe v8)
                _ -> coe v2
         MAlonzo.Code.Once.Surface.Syntax.C_inr''_130 v8
           -> case coe v0 of
                MAlonzo.Code.Once.Lang.Type.C__'43'__26 v9 v10
                  -> coe du_silentLoops_28 (coe v10) (coe v8)
                _ -> coe v2
         MAlonzo.Code.Once.Surface.Syntax.C_case''_152 v5 v6 v7 v8 v9 v10 v11 v13 v14 v15
           -> coe
                addInt
                (coe
                   addInt
                   (coe
                      du_silentLoops_28
                      (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v10) (coe v11))
                      (coe v13))
                   (coe du_silentLoops_28 (coe v0) (coe v14)))
                (coe du_silentLoops_28 (coe v0) (coe v15))
         MAlonzo.Code.Once.Surface.Syntax.C_absurd_168 v7
           -> coe
                du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
                (coe v7)
         MAlonzo.Code.Once.Surface.Syntax.C_let''_184 v5 v6 v7 v8 v10 v11
           -> coe
                addInt (coe du_silentLoops_28 (coe v0) (coe v11))
                (coe du_silentLoops_28 (coe v8) (coe v10))
         MAlonzo.Code.Once.Surface.Syntax.C_add_208 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                   (coe v7))
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_sub_218 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                   (coe v7))
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_mul_228 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                   (coe v7))
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_fadd_238 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                   (coe v7))
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_fsub_248 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                   (coe v7))
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_fmul_258 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                   (coe v7))
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                   (coe v7))
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_i2f_276 v6
           -> coe
                du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v6)
         MAlonzo.Code.Once.Surface.Syntax.C_div_286 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                   (coe v7))
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_mod''_296 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                   (coe v7))
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_neg_304 v6
           -> coe
                du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v6)
         MAlonzo.Code.Once.Surface.Syntax.C_lt_314 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                   (coe v7))
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_le_324 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                   (coe v7))
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_gt_334 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                   (coe v7))
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_ge_344 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                   (coe v7))
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_eq_354 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                   (coe v7))
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_ne_364 v5 v6 v7 v8
           -> coe
                addInt
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                   (coe v7))
                (coe
                   du_silentLoops_28 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                   (coe v8))
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v6 v8 v9
           -> coe du_silentLoops_28 (coe v6) (coe v9)
         MAlonzo.Code.Once.Surface.Syntax.C_closed_410 v6
           -> coe du_silentLoops_28 (coe v0) (coe v6)
         MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v5 v6 v8 v9
           -> coe du_silentLoops_28 (coe v6) (coe v9)
         MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v5 v6 v8 v11 v12
           -> case coe v0 of
                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v13 v14 v15
                  -> case coe v14 of
                       MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v16 v17
                         -> coe
                              addInt
                              (coe
                                 du_silentLoops_28
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v8)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v17))
                                    (coe v15))
                                 (coe v11))
                              (coe
                                 du_silentLoops_28
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v13)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v17))
                                    (coe v8))
                                 (coe v12))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v2
         MAlonzo.Code.Once.Surface.Syntax.C_copair''_470 v5 v6 v11 v12
           -> case coe v0 of
                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v13 v14 v15
                  -> case coe v13 of
                       MAlonzo.Code.Once.Lang.Type.C__'43'__26 v16 v17
                         -> case coe v14 of
                              MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v18 v19
                                -> coe
                                     addInt
                                     (coe
                                        du_silentLoops_28
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                           (coe v16)
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                              (coe v19))
                                           (coe v15))
                                        (coe v11))
                                     (coe
                                        du_silentLoops_28
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                           (coe v17)
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                              (coe v19))
                                           (coe v15))
                                        (coe v12))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v2
                _ -> coe v2
         MAlonzo.Code.Once.Surface.Syntax.C_fork''_488 v5 v6 v11 v12
           -> case coe v0 of
                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v13 v14 v15
                  -> case coe v14 of
                       MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v16 v17
                         -> case coe v15 of
                              MAlonzo.Code.Once.Lang.Type.C__'42'__24 v18 v19
                                -> coe
                                     addInt
                                     (coe
                                        du_silentLoops_28
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                           (coe v13)
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                              (coe v17))
                                           (coe v18))
                                        (coe v11))
                                     (coe
                                        du_silentLoops_28
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                           (coe v13)
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                              (coe v17))
                                           (coe v19))
                                        (coe v12))
                              _ -> coe v2
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v2
         MAlonzo.Code.Once.Surface.Syntax.C_curry''_506 v11
           -> case coe v0 of
                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v12 v13 v14
                  -> case coe v14 of
                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v15 v16 v17
                         -> case coe v16 of
                              MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v18 v19
                                -> coe
                                     du_silentLoops_28
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v12)
                                           (coe v15))
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v19))
                                        (coe v17))
                                     (coe v11)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v2
                _ -> coe v2
         MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v5 v9 v10
           -> case coe v0 of
                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v11 v12 v13
                  -> case coe v11 of
                       MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v14
                         -> case coe v12 of
                              MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v15 v16
                                -> coe
                                     du_silentLoops_28
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                                           (coe v14) (coe v13))
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v16))
                                        (coe v13))
                                     (coe v10)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v2
                _ -> coe v2
         MAlonzo.Code.Once.Surface.Syntax.C_ana_536 v5 v10 v11
           -> case coe v0 of
                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v12 v13 v14
                  -> case coe v14 of
                       MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v15 v16
                         -> coe
                              du_silentLoops_28
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v12)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.d_fin_46 (coe v16)))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v15)
                                    (coe v12)))
                              (coe v11)
                       _ -> coe v2
                _ -> coe v2
         MAlonzo.Code.Once.Surface.Syntax.C_loop_548 v5 v8
           -> case coe v0 of
                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v9 v10 v11
                  -> coe
                       addInt
                       (coe
                          MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                          (coe du_roundIsPure_16 (coe v8)) (coe (1 :: Integer))
                          (coe (0 :: Integer)))
                       (coe
                          du_silentLoops_28
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v9)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                             (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v11) (coe v9)))
                          (coe v8))
                _ -> coe v2
         _ -> coe v2)
