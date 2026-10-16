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
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade

-- Once.Surface.Thinning._⊆_
d__'8838'__10 a0 a1 a2 a3 = ()
data T__'8838'__10
  = C_done_12 | C_skip_26 T__'8838'__10 | C_keep_40 T__'8838'__10
-- Once.Surface.Thinning.⊆-refl
d_'8838''45'refl_46 ::
  Integer -> MAlonzo.Code.Once.Lang.Context.T_Ctx_6 -> T__'8838'__10
d_'8838''45'refl_46 ~v0 v1 = du_'8838''45'refl_46 v1
du_'8838''45'refl_46 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 -> T__'8838'__10
du_'8838''45'refl_46 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Context.C_'8709'_8 -> coe C_done_12
      MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v2 v3 v4
        -> coe C_keep_40 (coe du_'8838''45'refl_46 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Thinning.⊆-wk
d_'8838''45'wk_58 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 -> T__'8838'__10
d_'8838''45'wk_58 ~v0 v1 ~v2 ~v3 = du_'8838''45'wk_58 v1
du_'8838''45'wk_58 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 -> T__'8838'__10
du_'8838''45'wk_58 v0
  = coe C_skip_26 (coe du_'8838''45'refl_46 (coe v0))
-- Once.Surface.Thinning.thin-var
d_thin'45'var_68 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_thin'45'var_68 ~v0 ~v1 v2 v3 v4 v5
  = du_thin'45'var_68 v2 v3 v4 v5
du_thin'45'var_68 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_thin'45'var_68 v0 v1 v2 v3
  = case coe v2 of
      C_skip_26 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v12 v13 v14
               -> coe
                    MAlonzo.Code.Data.Fin.Base.C_suc_16
                    (coe du_thin'45'var_68 (coe v0) (coe v12) (coe v10) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_keep_40 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v12 v13 v14
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v16 v17 v18
                      -> case coe v3 of
                           MAlonzo.Code.Data.Fin.Base.C_zero_12
                             -> coe MAlonzo.Code.Data.Fin.Base.C_zero_12
                           MAlonzo.Code.Data.Fin.Base.C_suc_16 v20
                             -> coe
                                  MAlonzo.Code.Data.Fin.Base.C_suc_16
                                  (coe du_thin'45'var_68 (coe v12) (coe v16) (coe v10) (coe v20))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Thinning.thin-var-lookup
d_thin'45'var'45'lookup_92 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'var'45'lookup_92 = erased
-- Once.Surface.Thinning.thin-usage
d_thin'45'usage_112 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46
d_thin'45'usage_112 ~v0 ~v1 v2 v3 v4 v5
  = du_thin'45'usage_112 v2 v3 v4 v5
du_thin'45'usage_112 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46
du_thin'45'usage_112 v0 v1 v2 v3
  = case coe v2 of
      C_done_12
        -> coe
             seq (coe v3) (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
      C_skip_26 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v12 v13 v14
               -> coe
                    MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                    (coe du_thin'45'usage_112 (coe v0) (coe v12) (coe v10) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_keep_40 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v12 v13 v14
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v16 v17 v18
                      -> case coe v3 of
                           MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v20 v21
                             -> coe
                                  MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v20
                                  (coe du_thin'45'usage_112 (coe v12) (coe v16) (coe v10) (coe v21))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Thinning.thin-usage-+ᵘ
d_thin'45'usage'45''43''7512'_138 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'usage'45''43''7512'_138 = erased
-- Once.Surface.Thinning.thin-usage-*ᵘ
d_thin'45'usage'45''42''7512'_178 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'usage'45''42''7512'_178 = erased
-- Once.Surface.Thinning._.q*q-zero
d_q'42'q'45'zero_198 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_q'42'q'45'zero_198 = erased
-- Once.Surface.Thinning.thin-usage-⊔ᵘ
d_thin'45'usage'45''8852''7512'_232 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'usage'45''8852''7512'_232 = erased
-- Once.Surface.Thinning.thin-usage-⊑ᵘ
d_thin'45'usage'45''8849''7512'_272 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
d_thin'45'usage'45''8849''7512'_272 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_thin'45'usage'45''8849''7512'_272 v2 v3 v4 v5 v6 v7
du_thin'45'usage'45''8849''7512'_272 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
du_thin'45'usage'45''8849''7512'_272 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      C_done_12
        -> coe
             seq (coe v5)
             (coe MAlonzo.Code.Once.Lang.Context.C_'8849''91''93'_180)
      C_skip_26 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v14 v15 v16
               -> coe
                    MAlonzo.Code.Once.Lang.Context.C__'8849''8759'__192
                    (coe MAlonzo.Code.Once.Lang.Context.C_z'8804'z_164)
                    (coe
                       du_thin'45'usage'45''8849''7512'_272 (coe v0) (coe v14) (coe v12)
                       (coe v3) (coe v4) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_keep_40 v12
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v14 v15 v16
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v18 v19 v20
                      -> case coe v5 of
                           MAlonzo.Code.Once.Lang.Context.C__'8849''8759'__192 v26 v27
                             -> case coe v3 of
                                  MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v29 v30
                                    -> case coe v4 of
                                         MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v32 v33
                                           -> coe
                                                MAlonzo.Code.Once.Lang.Context.C__'8849''8759'__192
                                                v26
                                                (coe
                                                   du_thin'45'usage'45''8849''7512'_272 (coe v14)
                                                   (coe v18) (coe v12) (coe v30) (coe v33)
                                                   (coe v27))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Thinning.thin-usage-zeroUsage
d_thin'45'usage'45'zeroUsage_294 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  T__'8838'__10 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'usage'45'zeroUsage_294 = erased
-- Once.Surface.Thinning.thin-usage-refl
d_thin'45'usage'45'refl_310 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'usage'45'refl_310 = erased
-- Once.Surface.Thinning.thin-usage-singleUse
d_thin'45'usage'45'singleUse_332 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  T__'8838'__10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'usage'45'singleUse_332 = erased
