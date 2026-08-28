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

module MAlonzo.Code.Once.Surface.Context where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Type

-- Once.Surface.Context.Ctx
d_Ctx_6 a0 = ()
data T_Ctx_6
  = C_'8709'_8 |
    C__'44'_'94'__12 T_Ctx_6 MAlonzo.Code.Once.Type.T_Type_108
                     MAlonzo.Code.Once.Type.T_Quantity_4
-- Once.Surface.Context._,_
d__'44'__16 ::
  Integer -> T_Ctx_6 -> MAlonzo.Code.Once.Type.T_Type_108 -> T_Ctx_6
d__'44'__16 ~v0 v1 v2 = du__'44'__16 v1 v2
du__'44'__16 ::
  T_Ctx_6 -> MAlonzo.Code.Once.Type.T_Type_108 -> T_Ctx_6
du__'44'__16 v0 v1
  = coe C__'44'_'94'__12 v0 v1 (coe MAlonzo.Code.Once.Type.C_Many_10)
-- Once.Surface.Context.lookup
d_lookup_24 ::
  Integer ->
  T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Type_108
d_lookup_24 ~v0 v1 v2 = du_lookup_24 v1 v2
du_lookup_24 ::
  T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Type_108
du_lookup_24 v0 v1
  = case coe v0 of
      C__'44'_'94'__12 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v4
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe du_lookup_24 (coe v3) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Context.⟦_⟧ᶜ
d_'10214'_'10215''7580'_38 ::
  Integer -> T_Ctx_6 -> MAlonzo.Code.Once.Type.T_Type_108
d_'10214'_'10215''7580'_38 ~v0 v1 = du_'10214'_'10215''7580'_38 v1
du_'10214'_'10215''7580'_38 ::
  T_Ctx_6 -> MAlonzo.Code.Once.Type.T_Type_108
du_'10214'_'10215''7580'_38 v0
  = case coe v0 of
      C_'8709'_8 -> coe MAlonzo.Code.Once.Type.C_Unit_118
      C__'44'_'94'__12 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__122
             (coe du_'10214'_'10215''7580'_38 (coe v2)) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Context.lookupQuantity
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
-- Once.Surface.Context.Usage
d_Usage_60 a0 = ()
data T_Usage_60
  = C_'91''93'_62 |
    C__'8759'__66 MAlonzo.Code.Once.Type.T_Quantity_4 T_Usage_60
-- Once.Surface.Context.zeroUsage
d_zeroUsage_70 :: Integer -> T_Usage_60
d_zeroUsage_70 v0
  = case coe v0 of
      0 -> coe C_'91''93'_62
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                C__'8759'__66 (coe MAlonzo.Code.Once.Type.C_Zero_6)
                (d_zeroUsage_70 (coe v1)))
-- Once.Surface.Context.zeroUsage?
d_zeroUsage'63'_78 ::
  Integer ->
  T_Usage_60 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zeroUsage'63'_78 ~v0 v1 = du_zeroUsage'63'_78 v1
du_zeroUsage'63'_78 ::
  T_Usage_60 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
du_zeroUsage'63'_78 v0
  = case coe v0 of
      C_'91''93'_62
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
      C__'8759'__66 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_Zero_6 -> coe du_zeroUsage'63'_78 (coe v3)
             MAlonzo.Code.Once.Type.C_One_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Many_10
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Context.zeroUsage?-just
d_zeroUsage'63''45'just_92 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zeroUsage'63''45'just_92 = erased
-- Once.Surface.Context.singleUse
d_singleUse_102 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 -> T_Usage_60
d_singleUse_102 v0 v1 v2
  = let v3 = subInt (coe v0) (coe (1 :: Integer)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Data.Fin.Base.C_zero_12
           -> coe C__'8759'__66 v2 (d_zeroUsage_70 (coe v3))
         MAlonzo.Code.Data.Fin.Base.C_suc_16 v5
           -> coe
                C__'8759'__66 (coe MAlonzo.Code.Once.Type.C_Zero_6)
                (d_singleUse_102 (coe v3) (coe v5) (coe v2))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Surface.Context._+ᵘ_
d__'43''7512'__116 ::
  Integer -> T_Usage_60 -> T_Usage_60 -> T_Usage_60
d__'43''7512'__116 ~v0 v1 v2 = du__'43''7512'__116 v1 v2
du__'43''7512'__116 :: T_Usage_60 -> T_Usage_60 -> T_Usage_60
du__'43''7512'__116 v0 v1
  = case coe v0 of
      C_'91''93'_62 -> coe seq (coe v1) (coe v0)
      C__'8759'__66 v3 v4
        -> case coe v1 of
             C__'8759'__66 v6 v7
               -> coe
                    C__'8759'__66
                    (MAlonzo.Code.Once.Type.d__'43'q__12 (coe v3) (coe v6))
                    (coe du__'43''7512'__116 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Context._*ᵘ_
d__'42''7512'__128 ::
  Integer ->
  MAlonzo.Code.Once.Type.T_Quantity_4 -> T_Usage_60 -> T_Usage_60
d__'42''7512'__128 ~v0 v1 v2 = du__'42''7512'__128 v1 v2
du__'42''7512'__128 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 -> T_Usage_60 -> T_Usage_60
du__'42''7512'__128 v0 v1
  = case coe v1 of
      C_'91''93'_62 -> coe v1
      C__'8759'__66 v3 v4
        -> coe
             C__'8759'__66
             (MAlonzo.Code.Once.Type.d__'42'q__16 (coe v0) (coe v3))
             (coe du__'42''7512'__128 (coe v0) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Context._⊔ᵘ_
d__'8852''7512'__140 ::
  Integer -> T_Usage_60 -> T_Usage_60 -> T_Usage_60
d__'8852''7512'__140 ~v0 v1 v2 = du__'8852''7512'__140 v1 v2
du__'8852''7512'__140 :: T_Usage_60 -> T_Usage_60 -> T_Usage_60
du__'8852''7512'__140 v0 v1
  = case coe v0 of
      C_'91''93'_62 -> coe seq (coe v1) (coe v0)
      C__'8759'__66 v3 v4
        -> case coe v1 of
             C__'8759'__66 v6 v7
               -> coe
                    C__'8759'__66
                    (MAlonzo.Code.Once.Type.d__'8852'q__24 (coe v3) (coe v6))
                    (coe du__'8852''7512'__140 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Context._≤ᵘ_
d__'8804''7512'__152 :: Integer -> T_Usage_60 -> T_Ctx_6 -> ()
d__'8804''7512'__152 = erased
-- Once.Surface.Context._≤ᵘ?_
d__'8804''7512''63'__174 ::
  Integer -> T_Usage_60 -> T_Ctx_6 -> Bool
d__'8804''7512''63'__174 ~v0 v1 v2
  = du__'8804''7512''63'__174 v1 v2
du__'8804''7512''63'__174 :: T_Usage_60 -> T_Ctx_6 -> Bool
du__'8804''7512''63'__174 v0 v1
  = case coe v0 of
      C_'91''93'_62
        -> coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      C__'8759'__66 v3 v4
        -> case coe v1 of
             C__'44'_'94'__12 v6 v7 v8
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe MAlonzo.Code.Once.Type.d__'8804'q__28 (coe v3) (coe v8))
                    (coe du__'8804''7512''63'__174 (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Context.lookupUsage
d_lookupUsage_188 ::
  Integer ->
  T_Usage_60 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Quantity_4
d_lookupUsage_188 ~v0 v1 v2 = du_lookupUsage_188 v1 v2
du_lookupUsage_188 ::
  T_Usage_60 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Quantity_4
du_lookupUsage_188 v0 v1
  = case coe v0 of
      C__'8759'__66 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v3
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v6
               -> coe du_lookupUsage_188 (coe v4) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Context.tailUsage
d_tailUsage_202 :: Integer -> T_Usage_60 -> T_Usage_60
d_tailUsage_202 ~v0 v1 = du_tailUsage_202 v1
du_tailUsage_202 :: T_Usage_60 -> T_Usage_60
du_tailUsage_202 v0
  = case coe v0 of
      C__'8759'__66 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Context.SVar
d_SVar_210 a0 a1 a2 a3 = ()
newtype T_SVar_210 = C_svar_218 MAlonzo.Code.Data.Fin.Base.T_Fin_10
