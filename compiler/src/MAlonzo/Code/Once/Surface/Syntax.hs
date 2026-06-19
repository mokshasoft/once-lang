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
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Type

-- Once.Surface.Syntax.Ctx
d_Ctx_6 a0 = ()
data T_Ctx_6
  = C_'8709'_8 |
    C__'44'_'94'__12 T_Ctx_6 MAlonzo.Code.Once.Type.T_Type_112
                     MAlonzo.Code.Once.Type.T_Quantity_4
-- Once.Surface.Syntax._,_
d__'44'__16 ::
  Integer -> T_Ctx_6 -> MAlonzo.Code.Once.Type.T_Type_112 -> T_Ctx_6
d__'44'__16 ~v0 v1 v2 = du__'44'__16 v1 v2
du__'44'__16 ::
  T_Ctx_6 -> MAlonzo.Code.Once.Type.T_Type_112 -> T_Ctx_6
du__'44'__16 v0 v1
  = coe C__'44'_'94'__12 v0 v1 (coe MAlonzo.Code.Once.Type.C_Many_10)
-- Once.Surface.Syntax.lookup
d_lookup_24 ::
  Integer ->
  T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Type_112
d_lookup_24 ~v0 v1 v2 = du_lookup_24 v1 v2
du_lookup_24 ::
  T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Type_112
du_lookup_24 v0 v1
  = case coe v0 of
      C__'44'_'94'__12 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v4
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe du_lookup_24 (coe v3) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Syntax.⟦_⟧ᶜ
d_'10214'_'10215''7580'_38 ::
  Integer -> T_Ctx_6 -> MAlonzo.Code.Once.Type.T_Type_112
d_'10214'_'10215''7580'_38 ~v0 v1 = du_'10214'_'10215''7580'_38 v1
du_'10214'_'10215''7580'_38 ::
  T_Ctx_6 -> MAlonzo.Code.Once.Type.T_Type_112
du_'10214'_'10215''7580'_38 v0
  = case coe v0 of
      C_'8709'_8 -> coe MAlonzo.Code.Once.Type.C_Unit_122
      C__'44'_'94'__12 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__126
             (coe du_'10214'_'10215''7580'_38 (coe v2)) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Syntax.lookupQuantity
d_lookupQuantity_48 ::
  Integer ->
  T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Quantity_4
d_lookupQuantity_48 ~v0 v1 v2 = du_lookupQuantity_48 v1 v2
du_lookupQuantity_48 ::
  T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Quantity_4
du_lookupQuantity_48 v0 v1
  = case coe v0 of
      C__'44'_'94'__12 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v5
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe du_lookupQuantity_48 (coe v3) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Syntax.Usage
d_Usage_60 a0 = ()
data T_Usage_60
  = C_'91''93'_62 |
    C__'8759'__66 MAlonzo.Code.Once.Type.T_Quantity_4 T_Usage_60
-- Once.Surface.Syntax.zeroUsage
d_zeroUsage_70 :: Integer -> T_Usage_60
d_zeroUsage_70 v0
  = case coe v0 of
      0 -> coe C_'91''93'_62
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                C__'8759'__66 (coe MAlonzo.Code.Once.Type.C_Zero_6)
                (d_zeroUsage_70 (coe v1)))
-- Once.Surface.Syntax.singleUse
d_singleUse_76 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 -> T_Usage_60
d_singleUse_76 v0 v1 v2
  = let v3 = subInt (coe v0) (coe (1 :: Integer)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Data.Fin.Base.C_zero_12
           -> coe C__'8759'__66 v2 (d_zeroUsage_70 (coe v3))
         MAlonzo.Code.Data.Fin.Base.C_suc_16 v5
           -> coe
                C__'8759'__66 (coe MAlonzo.Code.Once.Type.C_Zero_6)
                (d_singleUse_76 (coe v3) (coe v5) (coe v2))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Surface.Syntax._+ᵘ_
d__'43''7512'__90 ::
  Integer -> T_Usage_60 -> T_Usage_60 -> T_Usage_60
d__'43''7512'__90 ~v0 v1 v2 = du__'43''7512'__90 v1 v2
du__'43''7512'__90 :: T_Usage_60 -> T_Usage_60 -> T_Usage_60
du__'43''7512'__90 v0 v1
  = case coe v0 of
      C_'91''93'_62 -> coe seq (coe v1) (coe v0)
      C__'8759'__66 v3 v4
        -> case coe v1 of
             C__'8759'__66 v6 v7
               -> coe
                    C__'8759'__66
                    (MAlonzo.Code.Once.Type.d__'43'q__12 (coe v3) (coe v6))
                    (coe du__'43''7512'__90 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Syntax._*ᵘ_
d__'42''7512'__102 ::
  Integer ->
  MAlonzo.Code.Once.Type.T_Quantity_4 -> T_Usage_60 -> T_Usage_60
d__'42''7512'__102 ~v0 v1 v2 = du__'42''7512'__102 v1 v2
du__'42''7512'__102 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 -> T_Usage_60 -> T_Usage_60
du__'42''7512'__102 v0 v1
  = case coe v1 of
      C_'91''93'_62 -> coe v1
      C__'8759'__66 v3 v4
        -> coe
             C__'8759'__66
             (MAlonzo.Code.Once.Type.d__'42'q__16 (coe v0) (coe v3))
             (coe du__'42''7512'__102 (coe v0) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Syntax._⊔ᵘ_
d__'8852''7512'__114 ::
  Integer -> T_Usage_60 -> T_Usage_60 -> T_Usage_60
d__'8852''7512'__114 ~v0 v1 v2 = du__'8852''7512'__114 v1 v2
du__'8852''7512'__114 :: T_Usage_60 -> T_Usage_60 -> T_Usage_60
du__'8852''7512'__114 v0 v1
  = case coe v0 of
      C_'91''93'_62 -> coe seq (coe v1) (coe v0)
      C__'8759'__66 v3 v4
        -> case coe v1 of
             C__'8759'__66 v6 v7
               -> coe
                    C__'8759'__66
                    (MAlonzo.Code.Once.Type.d__'8852'q__24 (coe v3) (coe v6))
                    (coe du__'8852''7512'__114 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Syntax._≤ᵘ_
d__'8804''7512'__126 :: Integer -> T_Usage_60 -> T_Ctx_6 -> ()
d__'8804''7512'__126 = erased
-- Once.Surface.Syntax._≤ᵘ?_
d__'8804''7512''63'__148 ::
  Integer -> T_Usage_60 -> T_Ctx_6 -> Bool
d__'8804''7512''63'__148 ~v0 v1 v2
  = du__'8804''7512''63'__148 v1 v2
du__'8804''7512''63'__148 :: T_Usage_60 -> T_Ctx_6 -> Bool
du__'8804''7512''63'__148 v0 v1
  = case coe v0 of
      C_'91''93'_62
        -> coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      C__'8759'__66 v3 v4
        -> case coe v1 of
             C__'44'_'94'__12 v6 v7 v8
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe MAlonzo.Code.Once.Type.d__'8804'q__28 (coe v3) (coe v8))
                    (coe du__'8804''7512''63'__148 (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Syntax.lookupUsage
d_lookupUsage_162 ::
  Integer ->
  T_Usage_60 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Quantity_4
d_lookupUsage_162 ~v0 v1 v2 = du_lookupUsage_162 v1 v2
du_lookupUsage_162 ::
  T_Usage_60 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Quantity_4
du_lookupUsage_162 v0 v1
  = case coe v0 of
      C__'8759'__66 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v3
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v6
               -> coe du_lookupUsage_162 (coe v4) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Syntax.tailUsage
d_tailUsage_176 :: Integer -> T_Usage_60 -> T_Usage_60
d_tailUsage_176 ~v0 v1 = du_tailUsage_176 v1
du_tailUsage_176 :: T_Usage_60 -> T_Usage_60
du_tailUsage_176 v0
  = case coe v0 of
      C__'8759'__66 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Syntax.Expr
d_Expr_184 a0 a1 a2 a3 = ()
data T_Expr_184
  = C_var_192 MAlonzo.Code.Data.Fin.Base.T_Fin_10 |
    C_lam_208 MAlonzo.Code.Once.Type.T_Quantity_4 T_Expr_184 |
    C_app_224 T_Usage_60 T_Usage_60 MAlonzo.Code.Once.Type.T_Type_112
              MAlonzo.Code.Once.Type.T_Quantity_4 T_Expr_184 T_Expr_184 |
    C_effApp_238 T_Usage_60 T_Usage_60
                 MAlonzo.Code.Once.Type.T_Type_112 T_Expr_184 T_Expr_184 |
    C_pair_252 T_Usage_60 T_Usage_60 T_Expr_184 T_Expr_184 |
    C_fst''_264 MAlonzo.Code.Once.Type.T_Type_112 T_Expr_184 |
    C_snd''_276 MAlonzo.Code.Once.Type.T_Type_112 T_Expr_184 |
    C_inl''_288 T_Expr_184 | C_inr''_300 T_Expr_184 |
    C_case''_322 T_Usage_60 T_Usage_60 T_Usage_60
                 MAlonzo.Code.Once.Type.T_Quantity_4
                 MAlonzo.Code.Once.Type.T_Quantity_4
                 MAlonzo.Code.Once.Type.T_Type_112 MAlonzo.Code.Once.Type.T_Type_112
                 T_Expr_184 T_Expr_184 T_Expr_184 |
    C_unit_328 | C_absurd_338 T_Expr_184 |
    C_let''_354 T_Usage_60 T_Usage_60
                MAlonzo.Code.Once.Type.T_Quantity_4
                MAlonzo.Code.Once.Type.T_Type_112 T_Expr_184 T_Expr_184 |
    C_int_360 Integer |
    C_str_366 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_add_376 T_Usage_60 T_Usage_60 T_Expr_184 T_Expr_184 |
    C_sub_386 T_Usage_60 T_Usage_60 T_Expr_184 T_Expr_184 |
    C_mul_396 T_Usage_60 T_Usage_60 T_Expr_184 T_Expr_184 |
    C_div_406 T_Usage_60 T_Usage_60 T_Expr_184 T_Expr_184 |
    C_mod''_416 T_Usage_60 T_Usage_60 T_Expr_184 T_Expr_184 |
    C_neg_424 T_Expr_184 |
    C_lt_434 T_Usage_60 T_Usage_60 T_Expr_184 T_Expr_184 |
    C_le_444 T_Usage_60 T_Usage_60 T_Expr_184 T_Expr_184 |
    C_gt_454 T_Usage_60 T_Usage_60 T_Expr_184 T_Expr_184 |
    C_ge_464 T_Usage_60 T_Usage_60 T_Expr_184 T_Expr_184 |
    C_eq_474 T_Usage_60 T_Usage_60 T_Expr_184 T_Expr_184 |
    C_ne_484 T_Usage_60 T_Usage_60 T_Expr_184 T_Expr_184 |
    C_arr''_496 T_Expr_184 |
    C_sigOp_504 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_closure_512 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_poly_522 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_lift'45'morphism_534 MAlonzo.Code.Once.CCC.IR.T_IR_274 |
    C_morph'45'app_546 T_Usage_60 MAlonzo.Code.Once.Type.T_Type_112
                       MAlonzo.Code.Once.CCC.IR.T_IR_274 T_Expr_184 |
    C_cata_558 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
               T_Expr_184 |
    C_ana_570 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
              T_Expr_184
