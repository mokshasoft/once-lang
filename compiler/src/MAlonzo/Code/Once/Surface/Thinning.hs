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

module MAlonzo.Code.Once.Surface.Thinning where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type

-- Once.Surface.Thinning._⊆_
d__'8838'__10 a0 a1 a2 a3 = ()
data T__'8838'__10
  = C_done_12 | C_skip_26 T__'8838'__10 | C_keep_40 T__'8838'__10
-- Once.Surface.Thinning.⊆-refl
d_'8838''45'refl_46 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
d_'8838''45'refl_46 ~v0 v1 = du_'8838''45'refl_46 v1
du_'8838''45'refl_46 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'refl_46 v0
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8 -> coe C_done_12
      MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v2 v3 v4
        -> coe C_keep_40 (coe du_'8838''45'refl_46 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Thinning.⊆-wk
d_'8838''45'wk_58 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 -> T__'8838'__10
d_'8838''45'wk_58 ~v0 v1 ~v2 ~v3 = du_'8838''45'wk_58 v1
du_'8838''45'wk_58 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'wk_58 v0
  = coe C_skip_26 (coe du_'8838''45'refl_46 (coe v0))
-- Once.Surface.Thinning._∘⊆_
d__'8728''8838'__72 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T__'8838'__10 -> T__'8838'__10 -> T__'8838'__10
d__'8728''8838'__72 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du__'8728''8838'__72 v3 v4 v5 v6 v7
du__'8728''8838'__72 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T__'8838'__10 -> T__'8838'__10 -> T__'8838'__10
du__'8728''8838'__72 v0 v1 v2 v3 v4
  = case coe v3 of
      C_done_12 -> coe seq (coe v4) (coe v3)
      C_skip_26 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v13 v14 v15
               -> coe
                    C_skip_26
                    (coe
                       du__'8728''8838'__72 (coe v0) (coe v1) (coe v13) (coe v11)
                       (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_keep_40 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v13 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v17 v18 v19
                      -> case coe v4 of
                           C_skip_26 v26
                             -> coe
                                  C_skip_26
                                  (coe
                                     du__'8728''8838'__72 (coe v0) (coe v13) (coe v17) (coe v11)
                                     (coe v26))
                           C_keep_40 v26
                             -> case coe v0 of
                                  MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v28 v29 v30
                                    -> coe
                                         C_keep_40
                                         (coe
                                            du__'8728''8838'__72 (coe v28) (coe v13) (coe v17)
                                            (coe v11) (coe v26))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Thinning.thin-var
d_thin'45'var_94 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_thin'45'var_94 ~v0 ~v1 v2 v3 v4 v5
  = du_thin'45'var_94 v2 v3 v4 v5
du_thin'45'var_94 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_thin'45'var_94 v0 v1 v2 v3
  = case coe v2 of
      C_skip_26 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v12 v13 v14
               -> coe
                    MAlonzo.Code.Data.Fin.Base.C_suc_16
                    (coe du_thin'45'var_94 (coe v0) (coe v12) (coe v10) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_keep_40 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v12 v13 v14
               -> case coe v1 of
                    MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v16 v17 v18
                      -> case coe v3 of
                           MAlonzo.Code.Data.Fin.Base.C_zero_12
                             -> coe MAlonzo.Code.Data.Fin.Base.C_zero_12
                           MAlonzo.Code.Data.Fin.Base.C_suc_16 v20
                             -> coe
                                  MAlonzo.Code.Data.Fin.Base.C_suc_16
                                  (coe du_thin'45'var_94 (coe v12) (coe v16) (coe v10) (coe v20))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Thinning.thin-var-lookup
d_thin'45'var'45'lookup_118 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'var'45'lookup_118 = erased
-- Once.Surface.Thinning.rename
d_rename_140 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_rename_140 ~v0 ~v1 v2 v3 v4 v5 v6 = du_rename_140 v2 v3 v4 v5 v6
du_rename_140 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
du_rename_140 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_170 v7
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_var_170
             (coe du_thin'45'var_94 (coe v0) (coe v1) (coe v3) (coe v7))
      MAlonzo.Code.Once.Surface.Syntax.C_lam_182 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v11 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_182
                    (coe
                       du_rename_140
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v0 v11
                          (coe MAlonzo.Code.Once.Type.C_Many_10))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v1) (coe v11))
                       (coe v13) (coe C_keep_40 v3) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_194 v7 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_194 v7 v9
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 (coe v7) (coe v9)
                   (coe v2))
                (coe v3) (coe v10))
             (coe du_rename_140 (coe v0) (coe v1) (coe v7) (coe v3) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_204 v7 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_effApp_204 v7
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Eff_44 (coe v7) (coe v2)) (coe v3)
                (coe v9))
             (coe du_rename_140 (coe v0) (coe v1) (coe v7) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_214 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'42'__38 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_214
                    (coe du_rename_140 (coe v0) (coe v1) (coe v11) (coe v3) (coe v9))
                    (coe du_rename_140 (coe v0) (coe v1) (coe v12) (coe v3) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_224 v8 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_224 v8
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v2) (coe v8)) (coe v3)
                (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_234 v7 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_234 v7
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v7) (coe v2)) (coe v3)
                (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_244 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'43'__40 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_244
                    (coe du_rename_140 (coe v0) (coe v1) (coe v10) (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_254 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'43'__40 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_254
                    (coe du_rename_140 (coe v0) (coe v1) (coe v11) (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_266 v7 v8 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_266 v7 v8
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v7) (coe v8)) (coe v3)
                (coe v10))
             (coe
                du_rename_140
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v0 v7
                   (coe MAlonzo.Code.Once.Type.C_Many_10))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v1) (coe v7))
                (coe v2) (coe C_keep_40 v3) (coe v11))
             (coe
                du_rename_140
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v0 v8
                   (coe MAlonzo.Code.Once.Type.C_Many_10))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v1) (coe v8))
                (coe v2) (coe C_keep_40 v3) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_272
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_272
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_280 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_280
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Void_36) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_290 v7 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_290 v7
             (coe du_rename_140 (coe v0) (coe v1) (coe v7) (coe v3) (coe v9))
             (coe
                du_rename_140
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v0 v7
                   (coe MAlonzo.Code.Once.Type.C_Many_10))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v1) (coe v7))
                (coe v2) (coe C_keep_40 v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_int_296 v7
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_int_296 v7
      MAlonzo.Code.Once.Surface.Syntax.C_str_302 v7
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_str_302 v7
      MAlonzo.Code.Once.Surface.Syntax.C_add_308 v7 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_add_308
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_314 v7 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_sub_314
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_320 v7 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mul_320
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_div_326 v7 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_div_326
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_332 v7 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mod''_332
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_338 v7
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_neg_338
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_344 v7 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lt_344
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_le_350 v7 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_le_350
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_356 v7 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_gt_356
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_362 v7 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ge_362
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_368 v7 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_eq_368
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_374 v7 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ne_374
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_arr''_384 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_Eff_44 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_arr''_384
                    (coe
                       du_rename_140 (coe v0) (coe v1)
                       (coe MAlonzo.Code.Once.Type.d__'8658'__64 (coe v10) (coe v11))
                       (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_roll''_392 v8
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_Fix_46 v9
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_roll''_392
                    (coe du_rename_140 (coe v0) (coe v1) (coe v9) (coe v3) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_unroll''_400 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_unroll''_400
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Fix_46 (coe v2)) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_prim_408 v8
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_prim_408 v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Thinning.Telescope
d_Telescope_302 a0 = ()
data T_Telescope_302
  = C_'91''93'_304 |
    C__'8759'__308 MAlonzo.Code.Once.Type.T_Type_32 T_Telescope_302
-- Once.Surface.Thinning.applyTel
d_applyTel_314 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T_Telescope_302 -> MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6
d_applyTel_314 ~v0 v1 v2 v3 = du_applyTel_314 v1 v2 v3
du_applyTel_314 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T_Telescope_302 -> MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6
du_applyTel_314 v0 v1 v2
  = case coe v0 of
      0 -> coe seq (coe v2) (coe v1)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                C__'8759'__308 v5 v6
                  -> coe
                       du_applyTel_314 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v1) (coe v5))
                       (coe v6)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Surface.Thinning.⊆-exch₀
d_'8838''45'exch'8320'_336 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> T__'8838'__10
d_'8838''45'exch'8320'_336 ~v0 v1 ~v2
  = du_'8838''45'exch'8320'_336 v1
du_'8838''45'exch'8320'_336 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8320'_336 v0
  = coe C_skip_26 (coe du_'8838''45'refl_46 (coe v0))
-- Once.Surface.Thinning.⊆-exch₁
d_'8838''45'exch'8321'_346 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> T__'8838'__10
d_'8838''45'exch'8321'_346 ~v0 v1 ~v2 ~v3
  = du_'8838''45'exch'8321'_346 v1
du_'8838''45'exch'8321'_346 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8321'_346 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8320'_336 (coe v0))
-- Once.Surface.Thinning.⊆-exch₂
d_'8838''45'exch'8322'_358 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> T__'8838'__10
d_'8838''45'exch'8322'_358 ~v0 v1 ~v2 ~v3 ~v4
  = du_'8838''45'exch'8322'_358 v1
du_'8838''45'exch'8322'_358 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8322'_358 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8321'_346 (coe v0))
-- Once.Surface.Thinning.⊆-exch₃
d_'8838''45'exch'8323'_372 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> T__'8838'__10
d_'8838''45'exch'8323'_372 ~v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_'8838''45'exch'8323'_372 v1
du_'8838''45'exch'8323'_372 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8323'_372 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8322'_358 (coe v0))
-- Once.Surface.Thinning.⊆-exch₄
d_'8838''45'exch'8324'_388 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> T__'8838'__10
d_'8838''45'exch'8324'_388 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8838''45'exch'8324'_388 v1
du_'8838''45'exch'8324'_388 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8324'_388 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8323'_372 (coe v0))
-- Once.Surface.Thinning.⊆-exch₅
d_'8838''45'exch'8325'_406 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> T__'8838'__10
d_'8838''45'exch'8325'_406 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_'8838''45'exch'8325'_406 v1
du_'8838''45'exch'8325'_406 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8325'_406 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8324'_388 (coe v0))
-- Once.Surface.Thinning.⊆-exch₆
d_'8838''45'exch'8326'_426 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> T__'8838'__10
d_'8838''45'exch'8326'_426 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_'8838''45'exch'8326'_426 v1
du_'8838''45'exch'8326'_426 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8326'_426 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8325'_406 (coe v0))
-- Once.Surface.Thinning.⊆-exch₇
d_'8838''45'exch'8327'_448 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> T__'8838'__10
d_'8838''45'exch'8327'_448 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_'8838''45'exch'8327'_448 v1
du_'8838''45'exch'8327'_448 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8327'_448 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8326'_426 (coe v0))
-- Once.Surface.Thinning.⊆-exch₈
d_'8838''45'exch'8328'_472 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> T__'8838'__10
d_'8838''45'exch'8328'_472 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10
  = du_'8838''45'exch'8328'_472 v1
du_'8838''45'exch'8328'_472 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8328'_472 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8327'_448 (coe v0))
-- Once.Surface.Thinning.weaken
d_weaken_484 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_weaken_484 ~v0 v1 v2 v3 v4 = du_weaken_484 v1 v2 v3 v4
du_weaken_484 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
du_weaken_484 v0 v1 v2 v3
  = coe
      du_rename_140 (coe v0)
      (coe MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v0 v1 v3)
      (coe v2) (coe du_'8838''45'wk_58 (coe v0))
-- Once.Surface.Thinning.exchange
d_exchange_496 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_exchange_496 ~v0 v1 v2 v3 v4 = du_exchange_496 v1 v2 v3 v4
du_exchange_496 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
du_exchange_496 v0 v1 v2 v3
  = coe
      du_rename_140
      (coe
         MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v2))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v1))
         (coe v2))
      (coe v3) (coe du_'8838''45'exch'8321'_346 (coe v0))
-- Once.Surface.Thinning.exchange₂
d_exchange'8322'_510 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_exchange'8322'_510 ~v0 v1 v2 v3 v4 v5
  = du_exchange'8322'_510 v1 v2 v3 v4 v5
du_exchange'8322'_510 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
du_exchange'8322'_510 v0 v1 v2 v3 v4
  = coe
      du_rename_140
      (coe
         MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v2))
         (coe v3))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v1))
            (coe v2))
         (coe v3))
      (coe v4) (coe du_'8838''45'exch'8322'_358 (coe v0))
-- Once.Surface.Thinning.exchange₃
d_exchange'8323'_526 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_exchange'8323'_526 ~v0 v1 v2 v3 v4 v5 v6
  = du_exchange'8323'_526 v1 v2 v3 v4 v5 v6
du_exchange'8323'_526 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
du_exchange'8323'_526 v0 v1 v2 v3 v4 v5
  = coe
      du_rename_140
      (coe
         MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v2))
            (coe v3))
         (coe v4))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v1))
               (coe v2))
            (coe v3))
         (coe v4))
      (coe v5) (coe du_'8838''45'exch'8323'_372 (coe v0))
-- Once.Surface.Thinning.exchange₄
d_exchange'8324'_544 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_exchange'8324'_544 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_exchange'8324'_544 v1 v2 v3 v4 v5 v6 v7
du_exchange'8324'_544 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
du_exchange'8324'_544 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_rename_140
      (coe
         MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v2))
               (coe v3))
            (coe v4))
         (coe v5))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v1))
                  (coe v2))
               (coe v3))
            (coe v4))
         (coe v5))
      (coe v6) (coe du_'8838''45'exch'8324'_388 (coe v0))
-- Once.Surface.Thinning.exchange₅
d_exchange'8325'_564 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_exchange'8325'_564 ~v0 v1 v2 v3 v4 v5 v6 v7 v8
  = du_exchange'8325'_564 v1 v2 v3 v4 v5 v6 v7 v8
du_exchange'8325'_564 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
du_exchange'8325'_564 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_rename_140
      (coe
         MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v2))
                  (coe v3))
               (coe v4))
            (coe v5))
         (coe v6))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v1))
                     (coe v2))
                  (coe v3))
               (coe v4))
            (coe v5))
         (coe v6))
      (coe v7) (coe du_'8838''45'exch'8325'_406 (coe v0))
-- Once.Surface.Thinning.exchange₆
d_exchange'8326'_586 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_exchange'8326'_586 ~v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du_exchange'8326'_586 v1 v2 v3 v4 v5 v6 v7 v8 v9
du_exchange'8326'_586 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
du_exchange'8326'_586 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_rename_140
      (coe
         MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v2))
                     (coe v3))
                  (coe v4))
               (coe v5))
            (coe v6))
         (coe v7))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v1))
                        (coe v2))
                     (coe v3))
                  (coe v4))
               (coe v5))
            (coe v6))
         (coe v7))
      (coe v8) (coe du_'8838''45'exch'8326'_426 (coe v0))
-- Once.Surface.Thinning.exchange₇
d_exchange'8327'_610 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_exchange'8327'_610 ~v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du_exchange'8327'_610 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
du_exchange'8327'_610 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
du_exchange'8327'_610 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_rename_140
      (coe
         MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v2))
                        (coe v3))
                     (coe v4))
                  (coe v5))
               (coe v6))
            (coe v7))
         (coe v8))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v1))
                           (coe v2))
                        (coe v3))
                     (coe v4))
                  (coe v5))
               (coe v6))
            (coe v7))
         (coe v8))
      (coe v9) (coe du_'8838''45'exch'8327'_448 (coe v0))
-- Once.Surface.Thinning.exchange₈
d_exchange'8328'_636 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_exchange'8328'_636 ~v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du_exchange'8328'_636 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
du_exchange'8328'_636 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
du_exchange'8328'_636 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_rename_140
      (coe
         MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v2))
                           (coe v3))
                        (coe v4))
                     (coe v5))
                  (coe v6))
               (coe v7))
            (coe v8))
         (coe v9))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v1))
                              (coe v2))
                           (coe v3))
                        (coe v4))
                     (coe v5))
                  (coe v6))
               (coe v7))
            (coe v8))
         (coe v9))
      (coe v10) (coe du_'8838''45'exch'8328'_472 (coe v0))
-- Once.Surface.Thinning.weakenFromEmpty
d_weakenFromEmpty_644 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_weakenFromEmpty_644 ~v0 v1 v2 v3
  = du_weakenFromEmpty_644 v1 v2 v3
du_weakenFromEmpty_644 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
du_weakenFromEmpty_644 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8 -> coe v2
      MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v4 v5 v6
        -> coe
             du_weaken_484 v4 v5 v1 v6
             (coe du_weakenFromEmpty_644 (coe v4) (coe v1) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
