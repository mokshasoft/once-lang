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

module MAlonzo.Code.Once.Surface.Syntax where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Type

-- Once.Surface.Syntax.Ctx
d_Ctx_6 a0 = ()
data T_Ctx_6
  = C_'8709'_8 |
    C__'44'_'94'__12 T_Ctx_6 MAlonzo.Code.Once.Type.T_Type_32
                     MAlonzo.Code.Once.Type.T_Quantity_4
-- Once.Surface.Syntax._,_
d__'44'__16 ::
  Integer -> T_Ctx_6 -> MAlonzo.Code.Once.Type.T_Type_32 -> T_Ctx_6
d__'44'__16 ~v0 v1 v2 = du__'44'__16 v1 v2
du__'44'__16 ::
  T_Ctx_6 -> MAlonzo.Code.Once.Type.T_Type_32 -> T_Ctx_6
du__'44'__16 v0 v1
  = coe C__'44'_'94'__12 v0 v1 (coe MAlonzo.Code.Once.Type.C_Many_10)
-- Once.Surface.Syntax.lookup
d_lookup_24 ::
  Integer ->
  T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Type_32
d_lookup_24 ~v0 v1 v2 = du_lookup_24 v1 v2
du_lookup_24 ::
  T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Type_32
du_lookup_24 v0 v1
  = case coe v0 of
      C__'44'_'94'__12 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v4
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe du_lookup_24 (coe v3) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Syntax.lookupQuantity
d_lookupQuantity_38 ::
  Integer ->
  T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Quantity_4
d_lookupQuantity_38 ~v0 v1 v2 = du_lookupQuantity_38 v1 v2
du_lookupQuantity_38 ::
  T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Quantity_4
du_lookupQuantity_38 v0 v1
  = case coe v0 of
      C__'44'_'94'__12 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v5
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe du_lookupQuantity_38 (coe v3) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Syntax.Usage
d_Usage_50 a0 = ()
data T_Usage_50
  = C_'91''93'_52 |
    C__'8759'__56 MAlonzo.Code.Once.Type.T_Quantity_4 T_Usage_50
-- Once.Surface.Syntax.zeroUsage
d_zeroUsage_60 :: Integer -> T_Usage_50
d_zeroUsage_60 v0
  = case coe v0 of
      0 -> coe C_'91''93'_52
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                C__'8759'__56 (coe MAlonzo.Code.Once.Type.C_Zero_6)
                (d_zeroUsage_60 (coe v1)))
-- Once.Surface.Syntax.singleUse
d_singleUse_66 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 -> T_Usage_50
d_singleUse_66 v0 v1 v2
  = let v3 = subInt (coe v0) (coe (1 :: Integer)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Data.Fin.Base.C_zero_12
           -> coe C__'8759'__56 v2 (d_zeroUsage_60 (coe v3))
         MAlonzo.Code.Data.Fin.Base.C_suc_16 v5
           -> coe
                C__'8759'__56 (coe MAlonzo.Code.Once.Type.C_Zero_6)
                (d_singleUse_66 (coe v3) (coe v5) (coe v2))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Surface.Syntax._+ᵘ_
d__'43''7512'__80 ::
  Integer -> T_Usage_50 -> T_Usage_50 -> T_Usage_50
d__'43''7512'__80 ~v0 v1 v2 = du__'43''7512'__80 v1 v2
du__'43''7512'__80 :: T_Usage_50 -> T_Usage_50 -> T_Usage_50
du__'43''7512'__80 v0 v1
  = case coe v0 of
      C_'91''93'_52 -> coe seq (coe v1) (coe v0)
      C__'8759'__56 v3 v4
        -> case coe v1 of
             C__'8759'__56 v6 v7
               -> coe
                    C__'8759'__56
                    (MAlonzo.Code.Once.Type.d__'43'q__12 (coe v3) (coe v6))
                    (coe du__'43''7512'__80 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Syntax._*ᵘ_
d__'42''7512'__92 ::
  Integer ->
  MAlonzo.Code.Once.Type.T_Quantity_4 -> T_Usage_50 -> T_Usage_50
d__'42''7512'__92 ~v0 v1 v2 = du__'42''7512'__92 v1 v2
du__'42''7512'__92 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 -> T_Usage_50 -> T_Usage_50
du__'42''7512'__92 v0 v1
  = case coe v1 of
      C_'91''93'_52 -> coe v1
      C__'8759'__56 v3 v4
        -> coe
             C__'8759'__56
             (MAlonzo.Code.Once.Type.d__'42'q__16 (coe v0) (coe v3))
             (coe du__'42''7512'__92 (coe v0) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Syntax._≤ᵘ_
d__'8804''7512'__104 :: Integer -> T_Usage_50 -> T_Ctx_6 -> ()
d__'8804''7512'__104 = erased
-- Once.Surface.Syntax._≤ᵘ?_
d__'8804''7512''63'__126 ::
  Integer -> T_Usage_50 -> T_Ctx_6 -> Bool
d__'8804''7512''63'__126 ~v0 v1 v2
  = du__'8804''7512''63'__126 v1 v2
du__'8804''7512''63'__126 :: T_Usage_50 -> T_Ctx_6 -> Bool
du__'8804''7512''63'__126 v0 v1
  = case coe v0 of
      C_'91''93'_52
        -> coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      C__'8759'__56 v3 v4
        -> case coe v1 of
             C__'44'_'94'__12 v6 v7 v8
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe MAlonzo.Code.Once.Type.d__'8804'q__28 (coe v3) (coe v8))
                    (coe du__'8804''7512''63'__126 (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Syntax.lookupUsage
d_lookupUsage_140 ::
  Integer ->
  T_Usage_50 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Quantity_4
d_lookupUsage_140 ~v0 v1 v2 = du_lookupUsage_140 v1 v2
du_lookupUsage_140 ::
  T_Usage_50 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Quantity_4
du_lookupUsage_140 v0 v1
  = case coe v0 of
      C__'8759'__56 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v3
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v6
               -> coe du_lookupUsage_140 (coe v4) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Syntax.tailUsage
d_tailUsage_154 :: Integer -> T_Usage_50 -> T_Usage_50
d_tailUsage_154 ~v0 v1 = du_tailUsage_154 v1
du_tailUsage_154 :: T_Usage_50 -> T_Usage_50
du_tailUsage_154 v0
  = case coe v0 of
      C__'8759'__56 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Syntax.Expr
d_Expr_162 a0 a1 a2 = ()
data T_Expr_162
  = C_var_170 MAlonzo.Code.Data.Fin.Base.T_Fin_10 |
    C_lam_182 T_Expr_162 |
    C_app_194 MAlonzo.Code.Once.Type.T_Type_32
              MAlonzo.Code.Once.Type.T_Quantity_4 T_Expr_162 T_Expr_162 |
    C_pair_204 T_Expr_162 T_Expr_162 |
    C_fst''_214 MAlonzo.Code.Once.Type.T_Type_32 T_Expr_162 |
    C_snd''_224 MAlonzo.Code.Once.Type.T_Type_32 T_Expr_162 |
    C_inl''_234 T_Expr_162 | C_inr''_244 T_Expr_162 |
    C_case''_256 MAlonzo.Code.Once.Type.T_Type_32
                 MAlonzo.Code.Once.Type.T_Type_32 T_Expr_162 T_Expr_162 T_Expr_162 |
    C_unit_262 | C_absurd_270 T_Expr_162 |
    C_let''_280 MAlonzo.Code.Once.Type.T_Type_32 T_Expr_162
                T_Expr_162 |
    C_int_286 Integer |
    C_str_292 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_add_298 T_Expr_162 T_Expr_162 | C_sub_304 T_Expr_162 T_Expr_162 |
    C_mul_310 T_Expr_162 T_Expr_162 | C_div_316 T_Expr_162 T_Expr_162 |
    C_mod''_322 T_Expr_162 T_Expr_162 | C_neg_328 T_Expr_162 |
    C_lt_334 T_Expr_162 T_Expr_162 | C_le_340 T_Expr_162 T_Expr_162 |
    C_gt_346 T_Expr_162 T_Expr_162 | C_ge_352 T_Expr_162 T_Expr_162 |
    C_eq_358 T_Expr_162 T_Expr_162 | C_ne_364 T_Expr_162 T_Expr_162 |
    C_arr''_374 T_Expr_162 | C_roll''_382 T_Expr_162 |
    C_unroll''_390 T_Expr_162
