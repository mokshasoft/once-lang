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

module MAlonzo.Code.Once.Spec.Context where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Spec.Context.Ctx
d_Ctx_8 a0 a1 = ()
data T_Ctx_8
  = C_'8709'_12 |
    C__'9656'__16 T_Ctx_8 MAlonzo.Code.Once.Spec.Type.T_Ty_8
-- Once.Spec.Context.lookup
d_lookup_22 ::
  Integer ->
  Integer ->
  T_Ctx_8 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_lookup_22 ~v0 ~v1 v2 v3 = du_lookup_22 v2 v3
du_lookup_22 ::
  T_Ctx_8 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_lookup_22 v0 v1
  = case coe v0 of
      C__'9656'__16 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v4
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v6
               -> coe du_lookup_22 (coe v3) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Context.Usage
d_Usage_34 a0 = ()
data T_Usage_34
  = C_'91''93'_36 |
    C__'8759'__40 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 T_Usage_34
-- Once.Spec.Context.zeroUsage
d_zeroUsage_44 :: Integer -> T_Usage_34
d_zeroUsage_44 v0
  = case coe v0 of
      0 -> coe C_'91''93'_36
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                C__'8759'__40 (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                (d_zeroUsage_44 (coe v1)))
-- Once.Spec.Context.singleUse
d_singleUse_50 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 -> T_Usage_34
d_singleUse_50 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe C__'8759'__40 v2 (d_zeroUsage_44 (coe v4)))
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v4
        -> let v5 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                C__'8759'__40 (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                (d_singleUse_50 (coe v5) (coe v4) (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Context._+ᵘ_
d__'43''7512'__60 ::
  Integer -> T_Usage_34 -> T_Usage_34 -> T_Usage_34
d__'43''7512'__60 ~v0 v1 v2 = du__'43''7512'__60 v1 v2
du__'43''7512'__60 :: T_Usage_34 -> T_Usage_34 -> T_Usage_34
du__'43''7512'__60 v0 v1
  = case coe v0 of
      C_'91''93'_36 -> coe seq (coe v1) (coe v0)
      C__'8759'__40 v3 v4
        -> case coe v1 of
             C__'8759'__40 v6 v7
               -> coe
                    C__'8759'__40
                    (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14 (coe v3) (coe v6))
                    (coe du__'43''7512'__60 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Context._*ᵘ_
d__'42''7512'__72 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  T_Usage_34 -> T_Usage_34
d__'42''7512'__72 ~v0 v1 v2 = du__'42''7512'__72 v1 v2
du__'42''7512'__72 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  T_Usage_34 -> T_Usage_34
du__'42''7512'__72 v0 v1
  = case coe v1 of
      C_'91''93'_36 -> coe v1
      C__'8759'__40 v3 v4
        -> coe
             C__'8759'__40
             (MAlonzo.Code.Once.Spec.Grade.d__'42'q__18 (coe v0) (coe v3))
             (coe du__'42''7512'__72 (coe v0) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Context._⊑ᵘ_
d__'8849''7512'__84 a0 a1 a2 = ()
data T__'8849''7512'__84
  = C_'91''93'_86 |
    C__'8849''8759'__98 MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22
                        T__'8849''7512'__84
-- Once.Spec.Context._⟨_⟩ᶜ
d__'10216'_'10217''7580'_106 ::
  Integer ->
  Integer ->
  Integer ->
  T_Ctx_8 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  T_Ctx_8
d__'10216'_'10217''7580'_106 v0 v1 ~v2 v3 v4
  = du__'10216'_'10217''7580'_106 v0 v1 v3 v4
du__'10216'_'10217''7580'_106 ::
  Integer ->
  Integer ->
  T_Ctx_8 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  T_Ctx_8
du__'10216'_'10217''7580'_106 v0 v1 v2 v3
  = case coe v2 of
      C_'8709'_12 -> coe v2
      C__'9656'__16 v5 v6
        -> coe
             C__'9656'__16
             (coe
                du__'10216'_'10217''7580'_106 (coe v0) (coe v1) (coe v5) (coe v3))
             (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'_154
                (coe v0) (coe v1) (coe v6) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
