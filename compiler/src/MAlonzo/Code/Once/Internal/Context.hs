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

module MAlonzo.Code.Once.Internal.Context where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type.Grade

-- Once.Internal.Context.Ctx
d_Ctx_8 :: Integer -> Integer -> ()
d_Ctx_8 = erased
-- Once.Internal.Context.lookup
d_lookup_20 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_lookup_20 ~v0 ~v1 = du_lookup_20
du_lookup_20 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_lookup_20 = coe MAlonzo.Code.Once.Spec.Context.du_lookup_22
-- Once.Internal.Context.⟦_⟧ᶜ
d_'10214'_'10215''7580'_26 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_'10214'_'10215''7580'_26 ~v0 ~v1 v2
  = du_'10214'_'10215''7580'_26 v2
du_'10214'_'10215''7580'_26 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_'10214'_'10215''7580'_26 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'8709'_12
        -> coe MAlonzo.Code.Once.Spec.Type.C_Unit_18
      MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe du_'10214'_'10215''7580'_26 (coe v2)) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Context.Usage
d_Usage_32 :: Integer -> ()
d_Usage_32 = erased
-- Once.Internal.Context.zeroUsage
d_zeroUsage_36 ::
  Integer -> MAlonzo.Code.Once.Spec.Context.T_Usage_34
d_zeroUsage_36 v0
  = coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44 (coe v0)
-- Once.Internal.Context.singleUse
d_singleUse_40 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34
d_singleUse_40 v0
  = coe MAlonzo.Code.Once.Spec.Context.d_singleUse_50 (coe v0)
-- Once.Internal.Context._+ᵘ_
d__'43''7512'__44 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34
d__'43''7512'__44 ~v0 = du__'43''7512'__44
du__'43''7512'__44 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34
du__'43''7512'__44
  = coe MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
-- Once.Internal.Context._*ᵘ_
d__'42''7512'__48 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34
d__'42''7512'__48 ~v0 = du__'42''7512'__48
du__'42''7512'__48 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34
du__'42''7512'__48
  = coe MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
-- Once.Internal.Context._⊔ᵘ_
d__'8852''7512'__52 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34
d__'8852''7512'__52 ~v0 v1 v2 = du__'8852''7512'__52 v1 v2
du__'8852''7512'__52 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34
du__'8852''7512'__52 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'91''93'_36
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v6 v7
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                    (MAlonzo.Code.Once.Type.Grade.d__'8852'q__20 (coe v3) (coe v6))
                    (coe du__'8852''7512'__52 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Context.SVar
d_SVar_66 a0 a1 a2 a3 a4 = ()
newtype T_SVar_66 = C_svar_76 MAlonzo.Code.Data.Fin.Base.T_Fin_10
-- Once.Internal.Context.liveCount
d_liveCount_80 ::
  Integer -> MAlonzo.Code.Once.Spec.Context.T_Usage_34 -> Integer
d_liveCount_80 ~v0 v1 = du_liveCount_80 v1
du_liveCount_80 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 -> Integer
du_liveCount_80 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'91''93'_36 -> coe (0 :: Integer)
      MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe du_liveCount_80 (coe v3)
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe addInt (coe (1 :: Integer)) (coe du_liveCount_80 (coe v3))
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe addInt (coe (1 :: Integer)) (coe du_liveCount_80 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Context._↾_
d__'8638'__94 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8
d__'8638'__94 ~v0 ~v1 v2 v3 = du__'8638'__94 v2 v3
du__'8638'__94 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8
du__'8638'__94 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'8709'_12
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe du__'8638'__94 (coe v3) (coe v7)
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           MAlonzo.Code.Once.Spec.Context.C__'9656'__16
                           (coe du__'8638'__94 (coe v3) (coe v7)) v4
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> coe
                           MAlonzo.Code.Once.Spec.Context.C__'9656'__16
                           (coe du__'8638'__94 (coe v3) (coe v7)) v4
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Context._≤q'_
d__'8804'q''__114 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 -> ()
d__'8804'q''__114 = erased
-- Once.Internal.Context._⊑ᵘ_
d__'8849''7512'__130 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 -> ()
d__'8849''7512'__130 = erased
-- Once.Internal.Context.⊑ᵘ-refl
d_'8849''7512''45'refl_138 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
d_'8849''7512''45'refl_138 ~v0 v1 = du_'8849''7512''45'refl_138 v1
du_'8849''7512''45'refl_138 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
du_'8849''7512''45'refl_138 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'91''93'_36
        -> coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_86
      MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (coe MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26)
                    (coe du_'8849''7512''45'refl_138 (coe v3))
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (coe MAlonzo.Code.Once.Spec.Grade.C_1'8804'1_28)
                    (coe du_'8849''7512''45'refl_138 (coe v3))
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (coe MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32)
                    (coe du_'8849''7512''45'refl_138 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Context.≤q'-+ˡ
d_'8804'q'''45''43''737'_150 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22
d_'8804'q'''45''43''737'_150 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26)
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe MAlonzo.Code.Once.Spec.Grade.C_1'8804'1_28
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe MAlonzo.Code.Once.Spec.Grade.C_1'8804'ω_30
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe MAlonzo.Code.Once.Spec.Grade.C_1'8804'ω_30
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_Many_12
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Context.≤q'-+ʳ
d_'8804'q'''45''43''691'_156 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22
d_'8804'q'''45''43''691'_156 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe MAlonzo.Code.Once.Spec.Grade.C_1'8804'1_28
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe MAlonzo.Code.Once.Spec.Grade.C_1'8804'ω_30
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_Many_12
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe MAlonzo.Code.Once.Spec.Grade.C_1'8804'ω_30
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Context.⊑ᵘ-+ˡ
d_'8849''7512''45''43''737'_164 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
d_'8849''7512''45''43''737'_164 ~v0 v1 v2
  = du_'8849''7512''45''43''737'_164 v1 v2
du_'8849''7512''45''43''737'_164 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
du_'8849''7512''45''43''737'_164 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'91''93'_36
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_86)
      MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v6 v7
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (d_'8804'q'''45''43''737'_150 (coe v3) (coe v6))
                    (coe du_'8849''7512''45''43''737'_164 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Context.⊑ᵘ-+ʳ
d_'8849''7512''45''43''691'_180 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
d_'8849''7512''45''43''691'_180 ~v0 v1 v2
  = du_'8849''7512''45''43''691'_180 v1 v2
du_'8849''7512''45''43''691'_180 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
du_'8849''7512''45''43''691'_180 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'91''93'_36
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_86)
      MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v6 v7
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (d_'8804'q'''45''43''691'_156 (coe v3) (coe v6))
                    (coe du_'8849''7512''45''43''691'_180 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Context.⊑q'-trans
d_'8849'q'''45'trans_196 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22
d_'8849'q'''45'trans_196 ~v0 v1 ~v2 v3 v4
  = du_'8849'q'''45'trans_196 v1 v3 v4
du_'8849'q'''45'trans_196 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22
du_'8849'q'''45'trans_196 v0 v1 v2
  = let v3
          = case coe v1 of
              MAlonzo.Code.Once.Spec.Grade.C_1'8804'1_28 -> coe v2
              MAlonzo.Code.Once.Spec.Grade.C_1'8804'ω_30
                -> coe seq (coe v2) (coe v1)
              MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32
                -> coe seq (coe v2) (coe v1)
              _ -> MAlonzo.RTE.mazUnreachableError in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Grade.C_Zero_8
           -> case coe v1 of
                MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26 -> coe v2
                MAlonzo.Code.Once.Spec.Grade.C_1'8804'1_28 -> coe v2
                MAlonzo.Code.Once.Spec.Grade.C_1'8804'ω_30
                  -> coe seq (coe v2) (coe v1)
                MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32
                  -> coe seq (coe v2) (coe v1)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Grade.C_One_10
           -> case coe v1 of
                MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26
                  -> case coe v2 of
                       MAlonzo.Code.Once.Spec.Grade.C_1'8804'1_28
                         -> coe MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26
                       MAlonzo.Code.Once.Spec.Grade.C_1'8804'ω_30
                         -> coe MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26
                       _ -> coe v3
                MAlonzo.Code.Once.Spec.Grade.C_1'8804'1_28 -> coe v2
                MAlonzo.Code.Once.Spec.Grade.C_1'8804'ω_30
                  -> coe seq (coe v2) (coe v1)
                MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32
                  -> coe seq (coe v2) (coe v1)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Grade.C_Many_12
           -> case coe v1 of
                MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26
                  -> case coe v2 of
                       MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32
                         -> coe MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26
                       _ -> coe v3
                MAlonzo.Code.Once.Spec.Grade.C_1'8804'1_28 -> coe v2
                MAlonzo.Code.Once.Spec.Grade.C_1'8804'ω_30
                  -> coe seq (coe v2) (coe v1)
                MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32
                  -> coe seq (coe v2) (coe v1)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Internal.Context._.z≤-any
d_z'8804''45'any_206 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22
d_z'8804''45'any_206 ~v0 ~v1 ~v2 v3 = du_z'8804''45'any_206 v3
du_z'8804''45'any_206 ::
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22
du_z'8804''45'any_206 v0 = coe v0
-- Once.Internal.Context.⊑ᵘ-trans
d_'8849''7512''45'trans_218 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
d_'8849''7512''45'trans_218 ~v0 v1 v2 v3 v4 v5
  = du_'8849''7512''45'trans_218 v1 v2 v3 v4 v5
du_'8849''7512''45'trans_218 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
du_'8849''7512''45'trans_218 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Spec.Context.C_'91''93'_86
        -> coe seq (coe v4) (coe v3)
      MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98 v10 v11
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v13 v14
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v16 v17
                      -> case coe v4 of
                           MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98 v23 v24
                             -> case coe v2 of
                                  MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v26 v27
                                    -> coe
                                         MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                                         (coe
                                            du_'8849'q'''45'trans_196 (coe v16) (coe v10) (coe v23))
                                         (coe
                                            du_'8849''7512''45'trans_218 (coe v14) (coe v17)
                                            (coe v27) (coe v11) (coe v24))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Context.⊑ᵘ-*One
d_'8849''7512''45''42'One_232 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
d_'8849''7512''45''42'One_232 ~v0 v1
  = du_'8849''7512''45''42'One_232 v1
du_'8849''7512''45''42'One_232 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
du_'8849''7512''45''42'One_232 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'91''93'_36
        -> coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_86
      MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (coe MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26)
                    (coe du_'8849''7512''45''42'One_232 (coe v3))
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (coe MAlonzo.Code.Once.Spec.Grade.C_1'8804'1_28)
                    (coe du_'8849''7512''45''42'One_232 (coe v3))
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (coe MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32)
                    (coe du_'8849''7512''45''42'One_232 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Context.⊑ᵘ-*Many
d_'8849''7512''45''42'Many_244 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
d_'8849''7512''45''42'Many_244 ~v0 v1
  = du_'8849''7512''45''42'Many_244 v1
du_'8849''7512''45''42'Many_244 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
du_'8849''7512''45''42'Many_244 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'91''93'_36
        -> coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_86
      MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (coe MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26)
                    (coe du_'8849''7512''45''42'Many_244 (coe v3))
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (coe MAlonzo.Code.Once.Spec.Grade.C_1'8804'ω_30)
                    (coe du_'8849''7512''45''42'Many_244 (coe v3))
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (coe MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32)
                    (coe du_'8849''7512''45''42'Many_244 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Context.≤q'-⊔ˡ
d_'8804'q'''45''8852''737'_256 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22
d_'8804'q'''45''8852''737'_256 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26)
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe MAlonzo.Code.Once.Spec.Grade.C_1'8804'1_28
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe MAlonzo.Code.Once.Spec.Grade.C_1'8804'1_28
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe MAlonzo.Code.Once.Spec.Grade.C_1'8804'ω_30
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_Many_12
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Context.≤q'-⊔ʳ
d_'8804'q'''45''8852''691'_262 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22
d_'8804'q'''45''8852''691'_262 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe MAlonzo.Code.Once.Spec.Grade.C_1'8804'1_28
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe MAlonzo.Code.Once.Spec.Grade.C_1'8804'1_28
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_Many_12
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe MAlonzo.Code.Once.Spec.Grade.C_1'8804'ω_30
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Context.⊑ᵘ-⊔ˡ
d_'8849''7512''45''8852''737'_270 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
d_'8849''7512''45''8852''737'_270 ~v0 v1 v2
  = du_'8849''7512''45''8852''737'_270 v1 v2
du_'8849''7512''45''8852''737'_270 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
du_'8849''7512''45''8852''737'_270 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'91''93'_36
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_86)
      MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v6 v7
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (d_'8804'q'''45''8852''737'_256 (coe v3) (coe v6))
                    (coe du_'8849''7512''45''8852''737'_270 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Context.⊑ᵘ-⊔ʳ
d_'8849''7512''45''8852''691'_286 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
d_'8849''7512''45''8852''691'_286 ~v0 v1 v2
  = du_'8849''7512''45''8852''691'_286 v1 v2
du_'8849''7512''45''8852''691'_286 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
du_'8849''7512''45''8852''691'_286 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'91''93'_36
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_86)
      MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v6 v7
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (d_'8804'q'''45''8852''691'_262 (coe v3) (coe v6))
                    (coe du_'8849''7512''45''8852''691'_286 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
