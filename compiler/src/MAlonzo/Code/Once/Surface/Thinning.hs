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
      MAlonzo.Code.Once.Surface.Syntax.C_pair_204 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'42'__38 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_204
                    (coe du_rename_140 (coe v0) (coe v1) (coe v11) (coe v3) (coe v9))
                    (coe du_rename_140 (coe v0) (coe v1) (coe v12) (coe v3) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_214 v8 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_214 v8
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v2) (coe v8)) (coe v3)
                (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_224 v7 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_224 v7
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v7) (coe v2)) (coe v3)
                (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_234 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'43'__40 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_234
                    (coe du_rename_140 (coe v0) (coe v1) (coe v10) (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_244 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'43'__40 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_244
                    (coe du_rename_140 (coe v0) (coe v1) (coe v11) (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_256 v7 v8 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_256 v7 v8
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
      MAlonzo.Code.Once.Surface.Syntax.C_unit_262
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_262
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_270 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_270
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Void_36) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_280 v7 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_280 v7
             (coe du_rename_140 (coe v0) (coe v1) (coe v7) (coe v3) (coe v9))
             (coe
                du_rename_140
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v0 v7
                   (coe MAlonzo.Code.Once.Type.C_Many_10))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v1) (coe v7))
                (coe v2) (coe C_keep_40 v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_int_286 v7
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_int_286 v7
      MAlonzo.Code.Once.Surface.Syntax.C_str_292 v7
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_str_292 v7
      MAlonzo.Code.Once.Surface.Syntax.C_add_298 v7 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_add_298
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_304 v7 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_sub_304
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_310 v7 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mul_310
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_div_316 v7 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_div_316
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_322 v7 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mod''_322
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_328 v7
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_neg_328
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_334 v7 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lt_334
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_le_340 v7 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_le_340
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_346 v7 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_gt_346
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_352 v7 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ge_352
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_358 v7 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_eq_358
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_364 v7 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ne_364
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v7))
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_arr''_374 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_Eff_44 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_arr''_374
                    (coe
                       du_rename_140 (coe v0) (coe v1)
                       (coe MAlonzo.Code.Once.Type.d__'8658'__64 (coe v10) (coe v11))
                       (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_roll''_382 v8
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_Fix_46 v9
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_roll''_382
                    (coe du_rename_140 (coe v0) (coe v1) (coe v9) (coe v3) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_unroll''_390 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_unroll''_390
             (coe
                du_rename_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Fix_46 (coe v2)) (coe v3) (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Thinning.Telescope
d_Telescope_292 a0 = ()
data T_Telescope_292
  = C_'91''93'_294 |
    C__'8759'__298 MAlonzo.Code.Once.Type.T_Type_32 T_Telescope_292
-- Once.Surface.Thinning.applyTel
d_applyTel_304 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T_Telescope_292 -> MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6
d_applyTel_304 ~v0 v1 v2 v3 = du_applyTel_304 v1 v2 v3
du_applyTel_304 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T_Telescope_292 -> MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6
du_applyTel_304 v0 v1 v2
  = case coe v0 of
      0 -> coe seq (coe v2) (coe v1)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                C__'8759'__298 v5 v6
                  -> coe
                       du_applyTel_304 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v1) (coe v5))
                       (coe v6)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Surface.Thinning.⊆-exch₀
d_'8838''45'exch'8320'_326 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> T__'8838'__10
d_'8838''45'exch'8320'_326 ~v0 v1 ~v2
  = du_'8838''45'exch'8320'_326 v1
du_'8838''45'exch'8320'_326 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8320'_326 v0
  = coe C_skip_26 (coe du_'8838''45'refl_46 (coe v0))
-- Once.Surface.Thinning.⊆-exch₁
d_'8838''45'exch'8321'_336 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> T__'8838'__10
d_'8838''45'exch'8321'_336 ~v0 v1 ~v2 ~v3
  = du_'8838''45'exch'8321'_336 v1
du_'8838''45'exch'8321'_336 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8321'_336 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8320'_326 (coe v0))
-- Once.Surface.Thinning.⊆-exch₂
d_'8838''45'exch'8322'_348 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> T__'8838'__10
d_'8838''45'exch'8322'_348 ~v0 v1 ~v2 ~v3 ~v4
  = du_'8838''45'exch'8322'_348 v1
du_'8838''45'exch'8322'_348 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8322'_348 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8321'_336 (coe v0))
-- Once.Surface.Thinning.⊆-exch₃
d_'8838''45'exch'8323'_362 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> T__'8838'__10
d_'8838''45'exch'8323'_362 ~v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_'8838''45'exch'8323'_362 v1
du_'8838''45'exch'8323'_362 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8323'_362 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8322'_348 (coe v0))
-- Once.Surface.Thinning.⊆-exch₄
d_'8838''45'exch'8324'_378 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> T__'8838'__10
d_'8838''45'exch'8324'_378 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8838''45'exch'8324'_378 v1
du_'8838''45'exch'8324'_378 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8324'_378 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8323'_362 (coe v0))
-- Once.Surface.Thinning.⊆-exch₅
d_'8838''45'exch'8325'_396 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> T__'8838'__10
d_'8838''45'exch'8325'_396 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_'8838''45'exch'8325'_396 v1
du_'8838''45'exch'8325'_396 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8325'_396 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8324'_378 (coe v0))
-- Once.Surface.Thinning.⊆-exch₆
d_'8838''45'exch'8326'_416 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> T__'8838'__10
d_'8838''45'exch'8326'_416 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_'8838''45'exch'8326'_416 v1
du_'8838''45'exch'8326'_416 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8326'_416 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8325'_396 (coe v0))
-- Once.Surface.Thinning.⊆-exch₇
d_'8838''45'exch'8327'_438 ::
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
d_'8838''45'exch'8327'_438 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_'8838''45'exch'8327'_438 v1
du_'8838''45'exch'8327'_438 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8327'_438 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8326'_416 (coe v0))
-- Once.Surface.Thinning.⊆-exch₈
d_'8838''45'exch'8328'_462 ::
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
d_'8838''45'exch'8328'_462 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10
  = du_'8838''45'exch'8328'_462 v1
du_'8838''45'exch'8328'_462 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8328'_462 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8327'_438 (coe v0))
-- Once.Surface.Thinning.weaken
d_weaken_474 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_weaken_474 ~v0 v1 v2 v3 v4 = du_weaken_474 v1 v2 v3 v4
du_weaken_474 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
du_weaken_474 v0 v1 v2 v3
  = coe
      du_rename_140 (coe v0)
      (coe MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v0 v1 v3)
      (coe v2) (coe du_'8838''45'wk_58 (coe v0))
-- Once.Surface.Thinning.exchange
d_exchange_486 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_exchange_486 ~v0 v1 v2 v3 v4 = du_exchange_486 v1 v2 v3 v4
du_exchange_486 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
du_exchange_486 v0 v1 v2 v3
  = coe
      du_rename_140
      (coe
         MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v2))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v1))
         (coe v2))
      (coe v3) (coe du_'8838''45'exch'8321'_336 (coe v0))
-- Once.Surface.Thinning.exchange₂
d_exchange'8322'_500 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_exchange'8322'_500 ~v0 v1 v2 v3 v4 v5
  = du_exchange'8322'_500 v1 v2 v3 v4 v5
du_exchange'8322'_500 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
du_exchange'8322'_500 v0 v1 v2 v3 v4
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
      (coe v4) (coe du_'8838''45'exch'8322'_348 (coe v0))
-- Once.Surface.Thinning.exchange₃
d_exchange'8323'_516 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_exchange'8323'_516 ~v0 v1 v2 v3 v4 v5 v6
  = du_exchange'8323'_516 v1 v2 v3 v4 v5 v6
du_exchange'8323'_516 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
du_exchange'8323'_516 v0 v1 v2 v3 v4 v5
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
      (coe v5) (coe du_'8838''45'exch'8323'_362 (coe v0))
-- Once.Surface.Thinning.exchange₄
d_exchange'8324'_534 ::
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
d_exchange'8324'_534 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_exchange'8324'_534 v1 v2 v3 v4 v5 v6 v7
du_exchange'8324'_534 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
du_exchange'8324'_534 v0 v1 v2 v3 v4 v5 v6
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
      (coe v6) (coe du_'8838''45'exch'8324'_378 (coe v0))
-- Once.Surface.Thinning.exchange₅
d_exchange'8325'_554 ::
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
d_exchange'8325'_554 ~v0 v1 v2 v3 v4 v5 v6 v7 v8
  = du_exchange'8325'_554 v1 v2 v3 v4 v5 v6 v7 v8
du_exchange'8325'_554 ::
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
du_exchange'8325'_554 v0 v1 v2 v3 v4 v5 v6 v7
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
      (coe v7) (coe du_'8838''45'exch'8325'_396 (coe v0))
-- Once.Surface.Thinning.exchange₆
d_exchange'8326'_576 ::
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
d_exchange'8326'_576 ~v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du_exchange'8326'_576 v1 v2 v3 v4 v5 v6 v7 v8 v9
du_exchange'8326'_576 ::
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
du_exchange'8326'_576 v0 v1 v2 v3 v4 v5 v6 v7 v8
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
      (coe v8) (coe du_'8838''45'exch'8326'_416 (coe v0))
-- Once.Surface.Thinning.exchange₇
d_exchange'8327'_600 ::
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
d_exchange'8327'_600 ~v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du_exchange'8327'_600 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
du_exchange'8327'_600 ::
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
du_exchange'8327'_600 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
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
      (coe v9) (coe du_'8838''45'exch'8327'_438 (coe v0))
-- Once.Surface.Thinning.exchange₈
d_exchange'8328'_626 ::
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
d_exchange'8328'_626 ~v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du_exchange'8328'_626 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
du_exchange'8328'_626 ::
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
du_exchange'8328'_626 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
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
      (coe v10) (coe du_'8838''45'exch'8328'_462 (coe v0))
-- Once.Surface.Thinning.weakenFromEmpty
d_weakenFromEmpty_634 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_weakenFromEmpty_634 ~v0 v1 v2 v3
  = du_weakenFromEmpty_634 v1 v2 v3
du_weakenFromEmpty_634 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
du_weakenFromEmpty_634 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8 -> coe v2
      MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v4 v5 v6
        -> coe
             du_weaken_474 v4 v5 v1 v6
             (coe du_weakenFromEmpty_634 (coe v4) (coe v1) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
