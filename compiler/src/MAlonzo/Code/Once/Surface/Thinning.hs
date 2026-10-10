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
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type

-- Once.Surface.Thinning._⊆_
d__'8838'__10 a0 a1 a2 a3 = ()
data T__'8838'__10
  = C_done_12 | C_skip_26 T__'8838'__10 | C_keep_40 T__'8838'__10
-- Once.Surface.Thinning.⊆-refl
d_'8838''45'refl_46 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> T__'8838'__10
d_'8838''45'refl_46 ~v0 v1 = du_'8838''45'refl_46 v1
du_'8838''45'refl_46 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> T__'8838'__10
du_'8838''45'refl_46 v0
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Context.C_'8709'_8 -> coe C_done_12
      MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v2 v3 v4
        -> coe C_keep_40 (coe du_'8838''45'refl_46 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Thinning.⊆-wk
d_'8838''45'wk_58 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 -> T__'8838'__10
d_'8838''45'wk_58 ~v0 v1 ~v2 ~v3 = du_'8838''45'wk_58 v1
du_'8838''45'wk_58 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> T__'8838'__10
du_'8838''45'wk_58 v0
  = coe C_skip_26 (coe du_'8838''45'refl_46 (coe v0))
-- Once.Surface.Thinning._∘⊆_
d__'8728''8838'__72 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T__'8838'__10 -> T__'8838'__10 -> T__'8838'__10
d__'8728''8838'__72 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du__'8728''8838'__72 v3 v4 v5 v6 v7
du__'8728''8838'__72 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T__'8838'__10 -> T__'8838'__10 -> T__'8838'__10
du__'8728''8838'__72 v0 v1 v2 v3 v4
  = case coe v3 of
      C_done_12 -> coe seq (coe v4) (coe v3)
      C_skip_26 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v13 v14 v15
               -> coe
                    C_skip_26
                    (coe
                       du__'8728''8838'__72 (coe v0) (coe v1) (coe v13) (coe v11)
                       (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_keep_40 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v13 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v17 v18 v19
                      -> case coe v4 of
                           C_skip_26 v26
                             -> coe
                                  C_skip_26
                                  (coe
                                     du__'8728''8838'__72 (coe v0) (coe v13) (coe v17) (coe v11)
                                     (coe v26))
                           C_keep_40 v26
                             -> case coe v0 of
                                  MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v28 v29 v30
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
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_thin'45'var_94 ~v0 ~v1 v2 v3 v4 v5
  = du_thin'45'var_94 v2 v3 v4 v5
du_thin'45'var_94 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_thin'45'var_94 v0 v1 v2 v3
  = case coe v2 of
      C_skip_26 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v12 v13 v14
               -> coe
                    MAlonzo.Code.Data.Fin.Base.C_suc_16
                    (coe du_thin'45'var_94 (coe v0) (coe v12) (coe v10) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_keep_40 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v12 v13 v14
               -> case coe v1 of
                    MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v16 v17 v18
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
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'var'45'lookup_118 = erased
-- Once.Surface.Thinning.thin-usage
d_thin'45'usage_138 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60
d_thin'45'usage_138 ~v0 ~v1 v2 v3 v4 v5
  = du_thin'45'usage_138 v2 v3 v4 v5
du_thin'45'usage_138 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60
du_thin'45'usage_138 v0 v1 v2 v3
  = case coe v2 of
      C_done_12
        -> coe
             seq (coe v3) (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
      C_skip_26 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v12 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                    (coe MAlonzo.Code.Once.Type.C_Zero_6)
                    (coe du_thin'45'usage_138 (coe v0) (coe v12) (coe v10) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_keep_40 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v12 v13 v14
               -> case coe v1 of
                    MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v16 v17 v18
                      -> case coe v3 of
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v20 v21
                             -> coe
                                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v20
                                  (coe du_thin'45'usage_138 (coe v12) (coe v16) (coe v10) (coe v21))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Thinning.thin-usage-+ᵘ
d_thin'45'usage'45''43''7512'_164 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'usage'45''43''7512'_164 = erased
-- Once.Surface.Thinning.thin-usage-*ᵘ
d_thin'45'usage'45''42''7512'_204 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'usage'45''42''7512'_204 = erased
-- Once.Surface.Thinning._.q*q-zero
d_q'42'q'45'zero_224 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_q'42'q'45'zero_224 = erased
-- Once.Surface.Thinning.thin-usage-⊔ᵘ
d_thin'45'usage'45''8852''7512'_258 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'usage'45''8852''7512'_258 = erased
-- Once.Surface.Thinning.thin-usage-⊑ᵘ
d_thin'45'usage'45''8849''7512'_298 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_thin'45'usage'45''8849''7512'_298 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_thin'45'usage'45''8849''7512'_298 v2 v3 v4 v5 v6 v7
du_thin'45'usage'45''8849''7512'_298 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_thin'45'usage'45''8849''7512'_298 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      C_done_12
        -> coe
             seq (coe v5)
             (coe MAlonzo.Code.Once.Surface.Context.C_'8849''91''93'_278)
      C_skip_26 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v14 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Context.C__'8849''8759'__290
                    (coe MAlonzo.Code.Once.Surface.Context.C_z'8804'z_262)
                    (coe
                       du_thin'45'usage'45''8849''7512'_298 (coe v0) (coe v14) (coe v12)
                       (coe v3) (coe v4) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_keep_40 v12
        -> case coe v0 of
             MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v14 v15 v16
               -> case coe v1 of
                    MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v18 v19 v20
                      -> case coe v5 of
                           MAlonzo.Code.Once.Surface.Context.C__'8849''8759'__290 v26 v27
                             -> case coe v3 of
                                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v29 v30
                                    -> case coe v4 of
                                         MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v32 v33
                                           -> coe
                                                MAlonzo.Code.Once.Surface.Context.C__'8849''8759'__290
                                                v26
                                                (coe
                                                   du_thin'45'usage'45''8849''7512'_298 (coe v14)
                                                   (coe v18) (coe v12) (coe v30) (coe v33)
                                                   (coe v27))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Thinning.thin-usage-zeroUsage
d_thin'45'usage'45'zeroUsage_320 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T__'8838'__10 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'usage'45'zeroUsage_320 = erased
-- Once.Surface.Thinning.thin-usage-refl
d_thin'45'usage'45'refl_336 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'usage'45'refl_336 = erased
-- Once.Surface.Thinning.thin-usage-singleUse
d_thin'45'usage'45'singleUse_358 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'usage'45'singleUse_358 = erased
-- Once.Surface.Thinning.substᵀ₂
d_subst'7488''8322'_406 ::
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
d_subst'7488''8322'_406 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 v12
  = du_subst'7488''8322'_406 v12
du_subst'7488''8322'_406 :: AgdaAny -> AgdaAny
du_subst'7488''8322'_406 v0 = coe v0
-- Once.Surface.Thinning.rename
d_rename_426 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_rename_426 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7
  = du_rename_426 v2 v3 v5 v6 v7
du_rename_426 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_rename_426 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_16 v7
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_var_16
             (coe du_thin'45'var_94 (coe v0) (coe v1) (coe v3) (coe v7))
      MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v8 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v15 v16 v17
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v8
                    (coe
                       du_rename_426
                       (coe
                          MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v0 v15
                          (coe MAlonzo.Code.Once.Type.C_Many_10))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v1 v15
                          (coe MAlonzo.Code.Once.Type.C_Many_10))
                       (coe v17) (coe C_keep_40 v3) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_50 v7 v8 v9 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_50
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8)) v9
             v11
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v9)
                   (coe
                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v11)
                      (coe MAlonzo.Code.Once.Type.C_pure_34))
                   (coe v2))
                (coe v3) (coe v12))
             (coe du_rename_426 (coe v0) (coe v1) (coe v9) (coe v3) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_64 v7 v8 v9 v11 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_effApp_64
                    (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
                    (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8)) v9
                    (coe
                       du_rename_426 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v9)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_eff_36))
                          (coe v15))
                       (coe v3) (coe v11))
                    (coe du_rename_426 (coe v0) (coe v1) (coe v9) (coe v3) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_78 v7 v8 v11 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'42'__124 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_78
                    (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
                    (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
                    (coe du_rename_426 (coe v0) (coe v1) (coe v13) (coe v3) (coe v11))
                    (coe du_rename_426 (coe v0) (coe v1) (coe v14) (coe v3) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_90 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_90 v9
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v2) (coe v9))
                (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_102 v8 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_102 v8
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v8) (coe v2))
                (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_114 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'43'__126 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_114
                    (coe du_rename_426 (coe v0) (coe v1) (coe v11) (coe v3) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_126 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'43'__126 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_126
                    (coe du_rename_426 (coe v0) (coe v1) (coe v12) (coe v3) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_148 v7 v8 v9 v10 v11 v12 v13 v15 v16 v17
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_148
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v9)) v10
             v11 v12 v13
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'43'__126 (coe v12) (coe v13))
                (coe v3) (coe v15))
             (coe
                du_rename_426
                (coe
                   MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v0 v12
                   (coe MAlonzo.Code.Once.Type.C_Many_10))
                (coe
                   MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v1 v12
                   (coe MAlonzo.Code.Once.Type.C_Many_10))
                (coe v2) (coe C_keep_40 v3) (coe v16))
             (coe
                du_rename_426
                (coe
                   MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v0 v13
                   (coe MAlonzo.Code.Once.Type.C_Many_10))
                (coe
                   MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v1 v13
                   (coe MAlonzo.Code.Once.Type.C_Many_10))
                (coe v2) (coe C_keep_40 v3) (coe v17))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_154
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_154
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_164 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_164
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Void_122) (coe v3) (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_180 v7 v8 v9 v10 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_180
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8)) v9
             v10
             (coe du_rename_426 (coe v0) (coe v1) (coe v10) (coe v3) (coe v12))
             (coe
                du_rename_426
                (coe
                   MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v0 v10
                   (coe MAlonzo.Code.Once.Type.C_Many_10))
                (coe
                   MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v1 v10
                   (coe MAlonzo.Code.Once.Type.C_Many_10))
                (coe v2) (coe C_keep_40 v3) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_int_186 v7
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_int_186 v7
      MAlonzo.Code.Once.Surface.Syntax.C_float_194 v7
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_float_194 v7
      MAlonzo.Code.Once.Surface.Syntax.C_add_204 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_add_204
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v9))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_214 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_sub_214
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v9))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_224 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mul_224
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v9))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_fadd_234 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fadd_234
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v3) (coe v9))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_fsub_244 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fsub_244
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v3) (coe v9))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_fmul_254 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fmul_254
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v3) (coe v9))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_fdiv_264 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fdiv_264
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v3) (coe v9))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_i2f_272 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_i2f_272
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_div_282 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_div_282
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v9))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_292 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mod''_292
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v9))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_300 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_neg_300
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_310 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lt_310
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v9))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_le_320 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_le_320
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v9))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_330 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_gt_330
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v9))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_340 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ge_340
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v9))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_350 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_eq_350
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v9))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_360 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ne_360
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v9))
             (coe
                du_rename_426 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_coerce_372 v8 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_coerce_372 v8 v10
             (coe du_rename_426 (coe v0) (coe v1) (coe v8) (coe v3) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_380 v8 v9
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_380 v8 v9
      MAlonzo.Code.Once.Surface.Syntax.C_closure_388 v8
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_closure_388 v8
      MAlonzo.Code.Once.Surface.Syntax.C_poly_398 v7
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_398 v7
      MAlonzo.Code.Once.Surface.Syntax.C_closed_406 v8
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_closed_406 v8
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418 v10
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418 v10
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v7 v8 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430
             (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7)) v8
             v10
             (coe du_rename_426 (coe v0) (coe v1) (coe v8) (coe v3) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_comp''_448 v7 v8 v10 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v15 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_comp''_448
                           (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
                           (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8)) v10
                           (coe
                              du_rename_426 (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v10)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v19))
                                 (coe v17))
                              (coe v3) (coe v13))
                           (coe
                              du_rename_426 (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v15)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v19))
                                 (coe v10))
                              (coe v3) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_copair''_466 v7 v8 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v15 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v18 v19
                      -> case coe v16 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v20 v21
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_copair''_466
                                  (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
                                  (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
                                  (coe
                                     du_rename_426 (coe v0) (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v18)
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v21))
                                        (coe v17))
                                     (coe v3) (coe v13))
                                  (coe
                                     du_rename_426 (coe v0) (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v19)
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v21))
                                        (coe v17))
                                     (coe v3) (coe v14))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fork''_484 v7 v8 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v15 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                      -> case coe v17 of
                           MAlonzo.Code.Once.Type.C__'42'__124 v20 v21
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_fork''_484
                                  (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7))
                                  (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v8))
                                  (coe
                                     du_rename_426 (coe v0) (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v15)
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v19))
                                        (coe v20))
                                     (coe v3) (coe v13))
                                  (coe
                                     du_rename_426 (coe v0) (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v15)
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v19))
                                        (coe v21))
                                     (coe v3) (coe v14))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_curry''_502 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v14 v15 v16
               -> case coe v16 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v17 v18 v19
                      -> case coe v18 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v20 v21
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_curry''_502
                                  (coe
                                     du_rename_426 (coe v0) (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'42'__124 (coe v14) (coe v17))
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v21))
                                        (coe v19))
                                     (coe v3) (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_cata_516 v7 v11 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v13 v14 v15
               -> case coe v13 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_130 v16
                      -> case coe v14 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v17 v18
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_cata_516
                                  (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7)) v11
                                  (coe
                                     du_rename_426 (coe v0) (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                        (coe
                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v16)
                                           (coe v15))
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v18))
                                        (coe v15))
                                     (coe v3) (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_532 v7 v12 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v14 v15 v16
               -> case coe v16 of
                    MAlonzo.Code.Once.Type.C_ν'45'type_132 v17 v18
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_ana_532
                           (coe du_thin'45'usage_138 (coe v0) (coe v1) (coe v3) (coe v7)) v12
                           (coe
                              du_rename_426 (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v14)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v18))
                                 (coe
                                    MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v17)
                                    (coe v14)))
                              (coe v3) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Thinning.Telescope
d_Telescope_922 a0 = ()
data T_Telescope_922
  = C_'91''93'_924 |
    C__'8759'__928 MAlonzo.Code.Once.Type.T_Type_108 T_Telescope_922
-- Once.Surface.Thinning.applyTel
d_applyTel_934 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T_Telescope_922 -> MAlonzo.Code.Once.Surface.Context.T_Ctx_6
d_applyTel_934 ~v0 v1 v2 v3 = du_applyTel_934 v1 v2 v3
du_applyTel_934 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T_Telescope_922 -> MAlonzo.Code.Once.Surface.Context.T_Ctx_6
du_applyTel_934 v0 v1 v2
  = case coe v0 of
      0 -> coe seq (coe v2) (coe v1)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                C__'8759'__928 v5 v6
                  -> coe
                       du_applyTel_934 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v5))
                       (coe v6)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Surface.Thinning.⊆-exch₀
d_'8838''45'exch'8320'_956 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T__'8838'__10
d_'8838''45'exch'8320'_956 ~v0 v1 ~v2
  = du_'8838''45'exch'8320'_956 v1
du_'8838''45'exch'8320'_956 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8320'_956 v0
  = coe C_skip_26 (coe du_'8838''45'refl_46 (coe v0))
-- Once.Surface.Thinning.⊆-exch₁
d_'8838''45'exch'8321'_966 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T__'8838'__10
d_'8838''45'exch'8321'_966 ~v0 v1 ~v2 ~v3
  = du_'8838''45'exch'8321'_966 v1
du_'8838''45'exch'8321'_966 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8321'_966 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8320'_956 (coe v0))
-- Once.Surface.Thinning.⊆-exch₂
d_'8838''45'exch'8322'_978 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T__'8838'__10
d_'8838''45'exch'8322'_978 ~v0 v1 ~v2 ~v3 ~v4
  = du_'8838''45'exch'8322'_978 v1
du_'8838''45'exch'8322'_978 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8322'_978 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8321'_966 (coe v0))
-- Once.Surface.Thinning.⊆-exch₃
d_'8838''45'exch'8323'_992 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T__'8838'__10
d_'8838''45'exch'8323'_992 ~v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_'8838''45'exch'8323'_992 v1
du_'8838''45'exch'8323'_992 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8323'_992 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8322'_978 (coe v0))
-- Once.Surface.Thinning.⊆-exch₄
d_'8838''45'exch'8324'_1008 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T__'8838'__10
d_'8838''45'exch'8324'_1008 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8838''45'exch'8324'_1008 v1
du_'8838''45'exch'8324'_1008 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8324'_1008 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8323'_992 (coe v0))
-- Once.Surface.Thinning.⊆-exch₅
d_'8838''45'exch'8325'_1026 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T__'8838'__10
d_'8838''45'exch'8325'_1026 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_'8838''45'exch'8325'_1026 v1
du_'8838''45'exch'8325'_1026 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8325'_1026 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8324'_1008 (coe v0))
-- Once.Surface.Thinning.⊆-exch₆
d_'8838''45'exch'8326'_1046 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T__'8838'__10
d_'8838''45'exch'8326'_1046 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_'8838''45'exch'8326'_1046 v1
du_'8838''45'exch'8326'_1046 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8326'_1046 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8325'_1026 (coe v0))
-- Once.Surface.Thinning.⊆-exch₇
d_'8838''45'exch'8327'_1068 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T__'8838'__10
d_'8838''45'exch'8327'_1068 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_'8838''45'exch'8327'_1068 v1
du_'8838''45'exch'8327'_1068 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8327'_1068 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8326'_1046 (coe v0))
-- Once.Surface.Thinning.⊆-exch₈
d_'8838''45'exch'8328'_1092 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T__'8838'__10
d_'8838''45'exch'8328'_1092 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10
  = du_'8838''45'exch'8328'_1092 v1
du_'8838''45'exch'8328'_1092 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> T__'8838'__10
du_'8838''45'exch'8328'_1092 v0
  = coe C_keep_40 (coe du_'8838''45'exch'8327'_1068 (coe v0))
-- Once.Surface.Thinning.weaken
d_weaken_1106 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_weaken_1106 ~v0 v1 ~v2 v3 v4 v5 v6
  = du_weaken_1106 v1 v3 v4 v5 v6
du_weaken_1106 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_weaken_1106 v0 v1 v2 v3 v4
  = coe
      du_rename_426 (coe v0)
      (coe MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v0 v1 v3)
      (coe v2) (coe du_'8838''45'wk_58 (coe v0)) (coe v4)
-- Once.Surface.Thinning.exchange
d_exchange_1128 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_exchange_1128 ~v0 v1 ~v2 v3 v4 v5 = du_exchange_1128 v1 v3 v4 v5
du_exchange_1128 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_exchange_1128 v0 v1 v2 v3
  = coe
      du_rename_426
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v2))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v1))
         (coe v2))
      (coe v3) (coe du_'8838''45'exch'8321'_966 (coe v0))
-- Once.Surface.Thinning.exchange₂
d_exchange'8322'_1144 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_exchange'8322'_1144 ~v0 v1 ~v2 v3 v4 v5 v6
  = du_exchange'8322'_1144 v1 v3 v4 v5 v6
du_exchange'8322'_1144 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_exchange'8322'_1144 v0 v1 v2 v3 v4
  = coe
      du_rename_426
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v2))
         (coe v3))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v1))
            (coe v2))
         (coe v3))
      (coe v4) (coe du_'8838''45'exch'8322'_978 (coe v0))
-- Once.Surface.Thinning.exchange₃
d_exchange'8323'_1162 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_exchange'8323'_1162 ~v0 v1 ~v2 v3 v4 v5 v6 v7
  = du_exchange'8323'_1162 v1 v3 v4 v5 v6 v7
du_exchange'8323'_1162 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_exchange'8323'_1162 v0 v1 v2 v3 v4 v5
  = coe
      du_rename_426
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v2))
            (coe v3))
         (coe v4))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'44'__16
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v1))
               (coe v2))
            (coe v3))
         (coe v4))
      (coe v5) (coe du_'8838''45'exch'8323'_992 (coe v0))
-- Once.Surface.Thinning.exchange₄
d_exchange'8324'_1182 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_exchange'8324'_1182 ~v0 v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_exchange'8324'_1182 v1 v3 v4 v5 v6 v7 v8
du_exchange'8324'_1182 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_exchange'8324'_1182 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_rename_426
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'44'__16
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v2))
               (coe v3))
            (coe v4))
         (coe v5))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'44'__16
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'44'__16
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v1))
                  (coe v2))
               (coe v3))
            (coe v4))
         (coe v5))
      (coe v6) (coe du_'8838''45'exch'8324'_1008 (coe v0))
-- Once.Surface.Thinning.exchange₅
d_exchange'8325'_1204 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_exchange'8325'_1204 ~v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9
  = du_exchange'8325'_1204 v1 v3 v4 v5 v6 v7 v8 v9
du_exchange'8325'_1204 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_exchange'8325'_1204 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_rename_426
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'44'__16
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'44'__16
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v2))
                  (coe v3))
               (coe v4))
            (coe v5))
         (coe v6))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'44'__16
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'44'__16
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'44'__16
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v1))
                     (coe v2))
                  (coe v3))
               (coe v4))
            (coe v5))
         (coe v6))
      (coe v7) (coe du_'8838''45'exch'8325'_1026 (coe v0))
-- Once.Surface.Thinning.exchange₆
d_exchange'8326'_1228 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_exchange'8326'_1228 ~v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du_exchange'8326'_1228 v1 v3 v4 v5 v6 v7 v8 v9 v10
du_exchange'8326'_1228 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_exchange'8326'_1228 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_rename_426
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'44'__16
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'44'__16
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'44'__16
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v2))
                     (coe v3))
                  (coe v4))
               (coe v5))
            (coe v6))
         (coe v7))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'44'__16
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'44'__16
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'44'__16
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'44'__16
                        (coe
                           MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v1))
                        (coe v2))
                     (coe v3))
                  (coe v4))
               (coe v5))
            (coe v6))
         (coe v7))
      (coe v8) (coe du_'8838''45'exch'8326'_1046 (coe v0))
-- Once.Surface.Thinning.exchange₇
d_exchange'8327'_1254 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_exchange'8327'_1254 ~v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du_exchange'8327'_1254 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11
du_exchange'8327'_1254 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_exchange'8327'_1254 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_rename_426
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'44'__16
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'44'__16
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'44'__16
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'44'__16
                        (coe
                           MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v2))
                        (coe v3))
                     (coe v4))
                  (coe v5))
               (coe v6))
            (coe v7))
         (coe v8))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'44'__16
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'44'__16
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'44'__16
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'44'__16
                        (coe
                           MAlonzo.Code.Once.Surface.Context.du__'44'__16
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v1))
                           (coe v2))
                        (coe v3))
                     (coe v4))
                  (coe v5))
               (coe v6))
            (coe v7))
         (coe v8))
      (coe v9) (coe du_'8838''45'exch'8327'_1068 (coe v0))
-- Once.Surface.Thinning.exchange₈
d_exchange'8328'_1282 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_exchange'8328'_1282 ~v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = du_exchange'8328'_1282 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_exchange'8328'_1282 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_exchange'8328'_1282 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_rename_426
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'44'__16
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'44'__16
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'44'__16
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'44'__16
                        (coe
                           MAlonzo.Code.Once.Surface.Context.du__'44'__16
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v2))
                           (coe v3))
                        (coe v4))
                     (coe v5))
                  (coe v6))
               (coe v7))
            (coe v8))
         (coe v9))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'44'__16
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'44'__16
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'44'__16
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'44'__16
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'44'__16
                        (coe
                           MAlonzo.Code.Once.Surface.Context.du__'44'__16
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'44'__16
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v1))
                              (coe v2))
                           (coe v3))
                        (coe v4))
                     (coe v5))
                  (coe v6))
               (coe v7))
            (coe v8))
         (coe v9))
      (coe v10) (coe du_'8838''45'exch'8328'_1092 (coe v0))
-- Once.Surface.Thinning.weakenFromEmpty
d_weakenFromEmpty_1290 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_weakenFromEmpty_1290 ~v0 v1 v2 v3
  = du_weakenFromEmpty_1290 v1 v2 v3
du_weakenFromEmpty_1290 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_weakenFromEmpty_1290 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Context.C_'8709'_8 -> coe v2
      MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v4 v5 v6
        -> coe
             du_weaken_1106 (coe v4) (coe v5) (coe v1) (coe v6)
             (coe du_weakenFromEmpty_1290 (coe v4) (coe v1) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
