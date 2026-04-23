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
import qualified MAlonzo.Code.Agda.Primitive
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
  MAlonzo.Code.Once.Type.T_Type_126 ->
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
-- Once.Surface.Thinning.thin-usage
d_thin'45'usage_138 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
d_thin'45'usage_138 ~v0 ~v1 v2 v3 v4 v5
  = du_thin'45'usage_138 v2 v3 v4 v5
du_thin'45'usage_138 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
du_thin'45'usage_138 v0 v1 v2 v3
  = case coe v2 of
      C_done_12
        -> coe
             seq (coe v3) (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52)
      C_skip_26 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v12 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                    (coe MAlonzo.Code.Once.Type.C_Zero_6)
                    (coe du_thin'45'usage_138 (coe v0) (coe v12) (coe v10) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_keep_40 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v12 v13 v14
               -> case coe v1 of
                    MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v16 v17 v18
                      -> case coe v3 of
                           MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56 v20 v21
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56 v20
                                  (coe du_thin'45'usage_138 (coe v12) (coe v16) (coe v10) (coe v21))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Thinning.thin-usage-+ᵘ
d_thin'45'usage'45''43''7512'_164 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'usage'45''43''7512'_164 = erased
-- Once.Surface.Thinning.thin-usage-*ᵘ
d_thin'45'usage'45''42''7512'_204 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'usage'45''42''7512'_204 = erased
-- Once.Surface.Thinning._.q*q-zero
d_q'42'q'45'zero_224 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_q'42'q'45'zero_224 = erased
-- Once.Surface.Thinning.thin-usage-⊔ᵘ
d_thin'45'usage'45''8852''7512'_258 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'usage'45''8852''7512'_258 = erased
-- Once.Surface.Thinning.thin-usage-zeroUsage
d_thin'45'usage'45'zeroUsage_294 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T__'8838'__10 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'usage'45'zeroUsage_294 = erased
-- Once.Surface.Thinning.thin-usage-refl
d_thin'45'usage'45'refl_310 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'usage'45'refl_310 = erased
-- Once.Surface.Thinning.thin-usage-singleUse
d_thin'45'usage'45'singleUse_332 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'usage'45'singleUse_332 = erased
-- Once.Surface.Thinning.rename
d_rename_374 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_rename_374 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7
  = du_rename_374 v2 v3 v5 v6 v7
du_rename_374 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_rename_374 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_182 v7
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_var_182
             (coe du_thin'45'var_94 (coe v0) (coe v1) (coe v3) (coe v7))
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198 v8 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__144 v14 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_198 v8
                    (coe
                       du_rename_374
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v0 v14
                          (coe MAlonzo.Code.Once.Type.C_Many_10))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v1 v14
                          (coe MAlonzo.Code.Once.Type.C_Many_10))
                       (coe v16) (coe C_keep_40 v3) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_214 v7 v8 v9 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_214
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8)) v9
             v11
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__144 (coe v9)
                   (coe
                      MAlonzo.Code.Once.Type.C_mk'45'kind_54 (coe v11)
                      (coe MAlonzo.Code.Once.Type.C_pure_38))
                   (coe v2))
                (coe v3) (coe v12))
             (coe du_rename_374 (coe v0) (coe v1) (coe v9) (coe v3) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_228 v7 v8 v9 v11 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__144 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_effApp_228
                    (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
                    (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8)) v9
                    (coe
                       du_rename_374 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__144 (coe v9)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_54
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_eff_40))
                          (coe v15))
                       (coe v3) (coe v11))
                    (coe du_rename_374 (coe v0) (coe v1) (coe v9) (coe v3) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_242 v7 v8 v11 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'42'__140 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_242
                    (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
                    (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
                    (coe du_rename_374 (coe v0) (coe v1) (coe v13) (coe v3) (coe v11))
                    (coe du_rename_374 (coe v0) (coe v1) (coe v14) (coe v3) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_254 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_254 v9
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'42'__140 (coe v2) (coe v9))
                (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_266 v8 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_266 v8
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'42'__140 (coe v8) (coe v2))
                (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_278 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'43'__142 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_278
                    (coe du_rename_374 (coe v0) (coe v1) (coe v11) (coe v3) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_290 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'43'__142 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_290
                    (coe du_rename_374 (coe v0) (coe v1) (coe v12) (coe v3) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_312 v7 v8 v9 v10 v11 v12 v13 v15 v16 v17
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_312
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v9)) v10
             v11 v12 v13
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'43'__142 (coe v12) (coe v13))
                (coe v3) (coe v15))
             (coe
                du_rename_374
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v0 v12
                   (coe MAlonzo.Code.Once.Type.C_Many_10))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v1 v12
                   (coe MAlonzo.Code.Once.Type.C_Many_10))
                (coe v2) (coe C_keep_40 v3) (coe v16))
             (coe
                du_rename_374
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v0 v13
                   (coe MAlonzo.Code.Once.Type.C_Many_10))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v1 v13
                   (coe MAlonzo.Code.Once.Type.C_Many_10))
                (coe v2) (coe C_keep_40 v3) (coe v17))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_318
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_318
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_328 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_328
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Void_138) (coe v3) (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_344 v7 v8 v9 v10 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_344
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8)) v9
             v10
             (coe du_rename_374 (coe v0) (coe v1) (coe v10) (coe v3) (coe v12))
             (coe
                du_rename_374
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v0 v10
                   (coe MAlonzo.Code.Once.Type.C_Many_10))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v1 v10
                   (coe MAlonzo.Code.Once.Type.C_Many_10))
                (coe v2) (coe C_keep_40 v3) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_int_350 v7
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_int_350 v7
      MAlonzo.Code.Once.Surface.Syntax.C_str_356 v7
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_str_356 v7
      MAlonzo.Code.Once.Surface.Syntax.C_add_366 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_add_366
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_150) (coe v3) (coe v9))
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_150) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_376 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_sub_376
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_150) (coe v3) (coe v9))
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_150) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_386 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mul_386
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_150) (coe v3) (coe v9))
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_150) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_div_396 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_div_396
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_150) (coe v3) (coe v9))
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_150) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_406 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mod''_406
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_150) (coe v3) (coe v9))
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_150) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_414 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_neg_414
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_150) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_424 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lt_424
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_150) (coe v3) (coe v9))
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_150) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_le_434 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_le_434
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_150) (coe v3) (coe v9))
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_150) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_444 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_gt_444
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_150) (coe v3) (coe v9))
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_150) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_454 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ge_454
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_150) (coe v3) (coe v9))
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_150) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_464 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_eq_464
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_150) (coe v3) (coe v9))
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_150) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_474 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ne_474
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_150) (coe v3) (coe v9))
             (coe
                du_rename_374 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_150) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_arr''_486 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__144 v11 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_arr''_486
                    (coe
                       du_rename_374 (coe v0) (coe v1)
                       (coe MAlonzo.Code.Once.Type.d__'8658'__164 (coe v11) (coe v13))
                       (coe v3) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494 v8
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494 v8
      MAlonzo.Code.Once.Surface.Syntax.C_poly_504 v7
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_504 v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Thinning._.subst₂
d_subst'8322'_406 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_subst'8322'_406 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18
  = du_subst'8322'_406 v18
du_subst'8322'_406 :: AgdaAny -> AgdaAny
du_subst'8322'_406 v0 = coe v0
-- Once.Surface.Thinning.Telescope
d_Telescope_726 a0 = ()
data T_Telescope_726
  = C_'91''93'_728 |
    C__'8759'__732 MAlonzo.Code.Once.Type.T_Type_126 T_Telescope_726
-- Once.Surface.Thinning.applyTel
d_applyTel_738 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T_Telescope_726 -> MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6
d_applyTel_738 ~v0 v1 v2 v3 = du_applyTel_738 v1 v2 v3
du_applyTel_738 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T_Telescope_726 -> MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6
du_applyTel_738 v0 v1 v2
  = case coe v0 of
      0 -> coe seq (coe v2) (coe v1)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                C__'8759'__732 v5 v6
                  -> coe
                       du_applyTel_738 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v1) (coe v5))
                       (coe v6)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Surface.Thinning.⊆-exch₀
d_'8838''45'exch'8320'_760 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126 -> T__'8838'__10
d_'8838''45'exch'8320'_760 ~v0 v1 ~v2
  = du_'8838''45'exch'8320'_760 v1
du_'8838''45'exch'8320'_760 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8320'_760 v0
  = coe C_skip_26 (coe du_'8838''45'refl_46 (coe v0))
-- Once.Surface.Thinning.⊆-exch₁
d_'8838''45'exch'8321'_770 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 -> T__'8838'__10
d_'8838''45'exch'8321'_770 ~v0 v1 ~v2 ~v3
  = du_'8838''45'exch'8321'_770 v1
du_'8838''45'exch'8321'_770 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8321'_770 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8320'_760 (coe v0))
-- Once.Surface.Thinning.⊆-exch₂
d_'8838''45'exch'8322'_782 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 -> T__'8838'__10
d_'8838''45'exch'8322'_782 ~v0 v1 ~v2 ~v3 ~v4
  = du_'8838''45'exch'8322'_782 v1
du_'8838''45'exch'8322'_782 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8322'_782 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8321'_770 (coe v0))
-- Once.Surface.Thinning.⊆-exch₃
d_'8838''45'exch'8323'_796 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 -> T__'8838'__10
d_'8838''45'exch'8323'_796 ~v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_'8838''45'exch'8323'_796 v1
du_'8838''45'exch'8323'_796 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8323'_796 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8322'_782 (coe v0))
-- Once.Surface.Thinning.⊆-exch₄
d_'8838''45'exch'8324'_812 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 -> T__'8838'__10
d_'8838''45'exch'8324'_812 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8838''45'exch'8324'_812 v1
du_'8838''45'exch'8324'_812 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8324'_812 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8323'_796 (coe v0))
-- Once.Surface.Thinning.⊆-exch₅
d_'8838''45'exch'8325'_830 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 -> T__'8838'__10
d_'8838''45'exch'8325'_830 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_'8838''45'exch'8325'_830 v1
du_'8838''45'exch'8325'_830 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8325'_830 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8324'_812 (coe v0))
-- Once.Surface.Thinning.⊆-exch₆
d_'8838''45'exch'8326'_850 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 -> T__'8838'__10
d_'8838''45'exch'8326'_850 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_'8838''45'exch'8326'_850 v1
du_'8838''45'exch'8326'_850 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8326'_850 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8325'_830 (coe v0))
-- Once.Surface.Thinning.⊆-exch₇
d_'8838''45'exch'8327'_872 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 -> T__'8838'__10
d_'8838''45'exch'8327'_872 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_'8838''45'exch'8327'_872 v1
du_'8838''45'exch'8327'_872 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8327'_872 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8326'_850 (coe v0))
-- Once.Surface.Thinning.⊆-exch₈
d_'8838''45'exch'8328'_896 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 -> T__'8838'__10
d_'8838''45'exch'8328'_896 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10
  = du_'8838''45'exch'8328'_896 v1
du_'8838''45'exch'8328'_896 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8328'_896 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8327'_872 (coe v0))
-- Once.Surface.Thinning.weaken
d_weaken_910 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_weaken_910 ~v0 v1 ~v2 v3 v4 v5 v6 = du_weaken_910 v1 v3 v4 v5 v6
du_weaken_910 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_weaken_910 v0 v1 v2 v3 v4
  = coe
      du_rename_374 (coe v0)
      (coe MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v0 v1 v3)
      (coe v2) (coe du_'8838''45'wk_58 (coe v0)) (coe v4)
-- Once.Surface.Thinning.exchange
d_exchange_932 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_exchange_932 ~v0 v1 ~v2 v3 v4 v5 = du_exchange_932 v1 v3 v4 v5
du_exchange_932 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_exchange_932 v0 v1 v2 v3
  = coe
      du_rename_374
      (coe
         MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v2))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v1))
         (coe v2))
      (coe v3) (coe du_'8838''45'exch'8321'_770 (coe v0))
-- Once.Surface.Thinning.exchange₂
d_exchange'8322'_948 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_exchange'8322'_948 ~v0 v1 ~v2 v3 v4 v5 v6
  = du_exchange'8322'_948 v1 v3 v4 v5 v6
du_exchange'8322'_948 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_exchange'8322'_948 v0 v1 v2 v3 v4
  = coe
      du_rename_374
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
      (coe v4) (coe du_'8838''45'exch'8322'_782 (coe v0))
-- Once.Surface.Thinning.exchange₃
d_exchange'8323'_966 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_exchange'8323'_966 ~v0 v1 ~v2 v3 v4 v5 v6 v7
  = du_exchange'8323'_966 v1 v3 v4 v5 v6 v7
du_exchange'8323'_966 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_exchange'8323'_966 v0 v1 v2 v3 v4 v5
  = coe
      du_rename_374
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
      (coe v5) (coe du_'8838''45'exch'8323'_796 (coe v0))
-- Once.Surface.Thinning.exchange₄
d_exchange'8324'_986 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_exchange'8324'_986 ~v0 v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_exchange'8324'_986 v1 v3 v4 v5 v6 v7 v8
du_exchange'8324'_986 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_exchange'8324'_986 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_rename_374
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
      (coe v6) (coe du_'8838''45'exch'8324'_812 (coe v0))
-- Once.Surface.Thinning.exchange₅
d_exchange'8325'_1008 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_exchange'8325'_1008 ~v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9
  = du_exchange'8325'_1008 v1 v3 v4 v5 v6 v7 v8 v9
du_exchange'8325'_1008 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_exchange'8325'_1008 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_rename_374
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
      (coe v7) (coe du_'8838''45'exch'8325'_830 (coe v0))
-- Once.Surface.Thinning.exchange₆
d_exchange'8326'_1032 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_exchange'8326'_1032 ~v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du_exchange'8326'_1032 v1 v3 v4 v5 v6 v7 v8 v9 v10
du_exchange'8326'_1032 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_exchange'8326'_1032 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_rename_374
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
      (coe v8) (coe du_'8838''45'exch'8326'_850 (coe v0))
-- Once.Surface.Thinning.exchange₇
d_exchange'8327'_1058 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_exchange'8327'_1058 ~v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du_exchange'8327'_1058 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11
du_exchange'8327'_1058 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_exchange'8327'_1058 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_rename_374
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
      (coe v9) (coe du_'8838''45'exch'8327'_872 (coe v0))
-- Once.Surface.Thinning.exchange₈
d_exchange'8328'_1086 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_exchange'8328'_1086 ~v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = du_exchange'8328'_1086 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_exchange'8328'_1086 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_exchange'8328'_1086 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_rename_374
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
      (coe v10) (coe du_'8838''45'exch'8328'_896 (coe v0))
-- Once.Surface.Thinning.weakenFromEmpty
d_weakenFromEmpty_1094 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_weakenFromEmpty_1094 ~v0 v1 v2 v3
  = du_weakenFromEmpty_1094 v1 v2 v3
du_weakenFromEmpty_1094 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_weakenFromEmpty_1094 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8 -> coe v2
      MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v4 v5 v6
        -> coe
             du_weaken_910 (coe v4) (coe v5) (coe v1) (coe v6)
             (coe du_weakenFromEmpty_1094 (coe v4) (coe v1) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
