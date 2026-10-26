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

module MAlonzo.Code.Once.Context where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type.Grade

-- Once.Context.⟦_⟧ᶜ
d_'10214'_'10215''7580'_14 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_'10214'_'10215''7580'_14 ~v0 ~v1 v2
  = du_'10214'_'10215''7580'_14 v2
du_'10214'_'10215''7580'_14 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_'10214'_'10215''7580'_14 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'8709'_12
        -> coe MAlonzo.Code.Once.Spec.Type.C_Unit_18
      MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe du_'10214'_'10215''7580'_14 (coe v2)) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Context._⊔ᵘ_
d__'8852''7512'__22 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34
d__'8852''7512'__22 ~v0 v1 v2 = du__'8852''7512'__22 v1 v2
du__'8852''7512'__22 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34
du__'8852''7512'__22 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'91''93'_36
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v6 v7
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                    (MAlonzo.Code.Once.Type.Grade.d__'8852'q__20 (coe v3) (coe v6))
                    (coe du__'8852''7512'__22 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Context.SVar
d_SVar_36 a0 a1 a2 a3 a4 = ()
newtype T_SVar_36 = C_svar_46 MAlonzo.Code.Data.Fin.Base.T_Fin_10
-- Once.Context.liveCount
d_liveCount_50 ::
  Integer -> MAlonzo.Code.Once.Spec.Context.T_Usage_34 -> Integer
d_liveCount_50 ~v0 v1 = du_liveCount_50 v1
du_liveCount_50 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 -> Integer
du_liveCount_50 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'91''93'_36 -> coe (0 :: Integer)
      MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe du_liveCount_50 (coe v3)
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe addInt (coe (1 :: Integer)) (coe du_liveCount_50 (coe v3))
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe addInt (coe (1 :: Integer)) (coe du_liveCount_50 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Context._↾_
d__'8638'__64 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8
d__'8638'__64 ~v0 ~v1 v2 v3 = du__'8638'__64 v2 v3
du__'8638'__64 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8
du__'8638'__64 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'8709'_12
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe du__'8638'__64 (coe v3) (coe v7)
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           MAlonzo.Code.Once.Spec.Context.C__'9656'__16
                           (coe du__'8638'__64 (coe v3) (coe v7)) v4
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> coe
                           MAlonzo.Code.Once.Spec.Context.C__'9656'__16
                           (coe du__'8638'__64 (coe v3) (coe v7)) v4
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Context.⊑ᵘ-refl
d_'8849''7512''45'refl_100 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
d_'8849''7512''45'refl_100 ~v0 v1 = du_'8849''7512''45'refl_100 v1
du_'8849''7512''45'refl_100 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
du_'8849''7512''45'refl_100 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'91''93'_36
        -> coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_86
      MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (coe MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26)
                    (coe du_'8849''7512''45'refl_100 (coe v3))
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (coe MAlonzo.Code.Once.Spec.Grade.C_1'8804'1_28)
                    (coe du_'8849''7512''45'refl_100 (coe v3))
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (coe MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32)
                    (coe du_'8849''7512''45'refl_100 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Context.≤q'-+ˡ
d_'8804'q'''45''43''737'_112 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22
d_'8804'q'''45''43''737'_112 v0 v1
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
-- Once.Context.≤q'-+ʳ
d_'8804'q'''45''43''691'_118 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22
d_'8804'q'''45''43''691'_118 v0 v1
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
-- Once.Context.⊑ᵘ-+ˡ
d_'8849''7512''45''43''737'_126 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
d_'8849''7512''45''43''737'_126 ~v0 v1 v2
  = du_'8849''7512''45''43''737'_126 v1 v2
du_'8849''7512''45''43''737'_126 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
du_'8849''7512''45''43''737'_126 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'91''93'_36
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_86)
      MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v6 v7
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (d_'8804'q'''45''43''737'_112 (coe v3) (coe v6))
                    (coe du_'8849''7512''45''43''737'_126 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Context.⊑ᵘ-+ʳ
d_'8849''7512''45''43''691'_142 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
d_'8849''7512''45''43''691'_142 ~v0 v1 v2
  = du_'8849''7512''45''43''691'_142 v1 v2
du_'8849''7512''45''43''691'_142 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
du_'8849''7512''45''43''691'_142 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'91''93'_36
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_86)
      MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v6 v7
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (d_'8804'q'''45''43''691'_118 (coe v3) (coe v6))
                    (coe du_'8849''7512''45''43''691'_142 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Context.⊑q'-trans
d_'8849'q'''45'trans_158 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22
d_'8849'q'''45'trans_158 ~v0 v1 ~v2 v3 v4
  = du_'8849'q'''45'trans_158 v1 v3 v4
du_'8849'q'''45'trans_158 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22
du_'8849'q'''45'trans_158 v0 v1 v2
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
-- Once.Context._.z≤-any
d_z'8804''45'any_168 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22
d_z'8804''45'any_168 ~v0 ~v1 ~v2 v3 = du_z'8804''45'any_168 v3
du_z'8804''45'any_168 ::
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22
du_z'8804''45'any_168 v0 = coe v0
-- Once.Context.⊑ᵘ-trans
d_'8849''7512''45'trans_180 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
d_'8849''7512''45'trans_180 ~v0 v1 v2 v3 v4 v5
  = du_'8849''7512''45'trans_180 v1 v2 v3 v4 v5
du_'8849''7512''45'trans_180 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
du_'8849''7512''45'trans_180 v0 v1 v2 v3 v4
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
                                            du_'8849'q'''45'trans_158 (coe v16) (coe v10) (coe v23))
                                         (coe
                                            du_'8849''7512''45'trans_180 (coe v14) (coe v17)
                                            (coe v27) (coe v11) (coe v24))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Context.⊑ᵘ-*One
d_'8849''7512''45''42'One_194 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
d_'8849''7512''45''42'One_194 ~v0 v1
  = du_'8849''7512''45''42'One_194 v1
du_'8849''7512''45''42'One_194 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
du_'8849''7512''45''42'One_194 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'91''93'_36
        -> coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_86
      MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (coe MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26)
                    (coe du_'8849''7512''45''42'One_194 (coe v3))
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (coe MAlonzo.Code.Once.Spec.Grade.C_1'8804'1_28)
                    (coe du_'8849''7512''45''42'One_194 (coe v3))
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (coe MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32)
                    (coe du_'8849''7512''45''42'One_194 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Context.⊑ᵘ-*Many
d_'8849''7512''45''42'Many_206 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
d_'8849''7512''45''42'Many_206 ~v0 v1
  = du_'8849''7512''45''42'Many_206 v1
du_'8849''7512''45''42'Many_206 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
du_'8849''7512''45''42'Many_206 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'91''93'_36
        -> coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_86
      MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (coe MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26)
                    (coe du_'8849''7512''45''42'Many_206 (coe v3))
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (coe MAlonzo.Code.Once.Spec.Grade.C_1'8804'ω_30)
                    (coe du_'8849''7512''45''42'Many_206 (coe v3))
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (coe MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32)
                    (coe du_'8849''7512''45''42'Many_206 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Context.≤q'-⊔ˡ
d_'8804'q'''45''8852''737'_218 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22
d_'8804'q'''45''8852''737'_218 v0 v1
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
-- Once.Context.≤q'-⊔ʳ
d_'8804'q'''45''8852''691'_224 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22
d_'8804'q'''45''8852''691'_224 v0 v1
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
-- Once.Context.⊑ᵘ-⊔ˡ
d_'8849''7512''45''8852''737'_232 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
d_'8849''7512''45''8852''737'_232 ~v0 v1 v2
  = du_'8849''7512''45''8852''737'_232 v1 v2
du_'8849''7512''45''8852''737'_232 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
du_'8849''7512''45''8852''737'_232 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'91''93'_36
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_86)
      MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v6 v7
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (d_'8804'q'''45''8852''737'_218 (coe v3) (coe v6))
                    (coe du_'8849''7512''45''8852''737'_232 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Context.⊑ᵘ-⊔ʳ
d_'8849''7512''45''8852''691'_248 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
d_'8849''7512''45''8852''691'_248 ~v0 v1 v2
  = du_'8849''7512''45''8852''691'_248 v1 v2
du_'8849''7512''45''8852''691'_248 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84
du_'8849''7512''45''8852''691'_248 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'91''93'_36
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_86)
      MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v6 v7
               -> coe
                    MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98
                    (d_'8804'q'''45''8852''691'_224 (coe v3) (coe v6))
                    (coe du_'8849''7512''45''8852''691'_248 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Context.≤q'-unique
d_'8804'q'''45'unique_266 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804'q'''45'unique_266 = erased
-- Once.Context.⊑ᵘ-unique
d_'8849''7512''45'unique_278 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8849''7512''45'unique_278 = erased
