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

module MAlonzo.Code.Once.Lang.Context where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade

-- Once.Lang.Context.Ctx
d_Ctx_6 a0 = ()
data T_Ctx_6
  = C_'8709'_8 |
    C__'44'_'94'__12 T_Ctx_6 MAlonzo.Code.Once.Lang.Type.T_Type_8
                     MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
-- Once.Lang.Context._,_
d__'44'__16 ::
  Integer ->
  T_Ctx_6 -> MAlonzo.Code.Once.Lang.Type.T_Type_8 -> T_Ctx_6
d__'44'__16 ~v0 v1 v2 = du__'44'__16 v1 v2
du__'44'__16 ::
  T_Ctx_6 -> MAlonzo.Code.Once.Lang.Type.T_Type_8 -> T_Ctx_6
du__'44'__16 v0 v1
  = coe
      C__'44'_'94'__12 v0 v1
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
-- Once.Lang.Context.lookup
d_lookup_24 ::
  Integer ->
  T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
d_lookup_24 ~v0 v1 v2 = du_lookup_24 v1 v2
du_lookup_24 ::
  T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_lookup_24 v0 v1
  = case coe v0 of
      C__'44'_'94'__12 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v4
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe du_lookup_24 (coe v3) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Context.⟦_⟧ᶜ
d_'10214'_'10215''7580'_38 ::
  Integer -> T_Ctx_6 -> MAlonzo.Code.Once.Lang.Type.T_Type_8
d_'10214'_'10215''7580'_38 ~v0 v1 = du_'10214'_'10215''7580'_38 v1
du_'10214'_'10215''7580'_38 ::
  T_Ctx_6 -> MAlonzo.Code.Once.Lang.Type.T_Type_8
du_'10214'_'10215''7580'_38 v0
  = case coe v0 of
      C_'8709'_8 -> coe MAlonzo.Code.Once.Lang.Type.C_Unit_20
      C__'44'_'94'__12 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Type.C__'42'__24
             (coe du_'10214'_'10215''7580'_38 (coe v2)) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Context.Usage
d_Usage_46 a0 = ()
data T_Usage_46
  = C_'91''93'_48 |
    C__'8759'__52 MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
                  T_Usage_46
-- Once.Lang.Context.zeroUsage
d_zeroUsage_56 :: Integer -> T_Usage_46
d_zeroUsage_56 v0
  = case coe v0 of
      0 -> coe C_'91''93'_48
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                C__'8759'__52 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                (d_zeroUsage_56 (coe v1)))
-- Once.Lang.Context.singleUse
d_singleUse_62 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 -> T_Usage_46
d_singleUse_62 v0 v1 v2
  = let v3 = subInt (coe v0) (coe (1 :: Integer)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Data.Fin.Base.C_zero_12
           -> coe C__'8759'__52 v2 (d_zeroUsage_56 (coe v3))
         MAlonzo.Code.Data.Fin.Base.C_suc_16 v5
           -> coe
                C__'8759'__52 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                (d_singleUse_62 (coe v3) (coe v5) (coe v2))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Lang.Context._+ᵘ_
d__'43''7512'__76 ::
  Integer -> T_Usage_46 -> T_Usage_46 -> T_Usage_46
d__'43''7512'__76 ~v0 v1 v2 = du__'43''7512'__76 v1 v2
du__'43''7512'__76 :: T_Usage_46 -> T_Usage_46 -> T_Usage_46
du__'43''7512'__76 v0 v1
  = case coe v0 of
      C_'91''93'_48 -> coe seq (coe v1) (coe v0)
      C__'8759'__52 v3 v4
        -> case coe v1 of
             C__'8759'__52 v6 v7
               -> coe
                    C__'8759'__52
                    (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16 (coe v3) (coe v6))
                    (coe du__'43''7512'__76 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Context._*ᵘ_
d__'42''7512'__88 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  T_Usage_46 -> T_Usage_46
d__'42''7512'__88 ~v0 v1 v2 = du__'42''7512'__88 v1 v2
du__'42''7512'__88 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  T_Usage_46 -> T_Usage_46
du__'42''7512'__88 v0 v1
  = case coe v1 of
      C_'91''93'_48 -> coe v1
      C__'8759'__52 v3 v4
        -> coe
             C__'8759'__52
             (MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20 (coe v0) (coe v3))
             (coe du__'42''7512'__88 (coe v0) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Context._⊔ᵘ_
d__'8852''7512'__100 ::
  Integer -> T_Usage_46 -> T_Usage_46 -> T_Usage_46
d__'8852''7512'__100 ~v0 v1 v2 = du__'8852''7512'__100 v1 v2
du__'8852''7512'__100 :: T_Usage_46 -> T_Usage_46 -> T_Usage_46
du__'8852''7512'__100 v0 v1
  = case coe v0 of
      C_'91''93'_48 -> coe seq (coe v1) (coe v0)
      C__'8759'__52 v3 v4
        -> case coe v1 of
             C__'8759'__52 v6 v7
               -> coe
                    C__'8759'__52
                    (MAlonzo.Code.Once.Lang.Type.Grade.d__'8852'q__22
                       (coe v3) (coe v6))
                    (coe du__'8852''7512'__100 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Context.SVar
d_SVar_112 a0 a1 a2 a3 = ()
newtype T_SVar_112 = C_svar_120 MAlonzo.Code.Data.Fin.Base.T_Fin_10
-- Once.Lang.Context.liveCount
d_liveCount_124 :: Integer -> T_Usage_46 -> Integer
d_liveCount_124 ~v0 v1 = du_liveCount_124 v1
du_liveCount_124 :: T_Usage_46 -> Integer
du_liveCount_124 v0
  = case coe v0 of
      C_'91''93'_48 -> coe (0 :: Integer)
      C__'8759'__52 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
               -> coe du_liveCount_124 (coe v3)
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
               -> coe addInt (coe (1 :: Integer)) (coe du_liveCount_124 (coe v3))
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
               -> coe addInt (coe (1 :: Integer)) (coe du_liveCount_124 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Context._↾_
d__'8638'__136 :: Integer -> T_Ctx_6 -> T_Usage_46 -> T_Ctx_6
d__'8638'__136 ~v0 v1 v2 = du__'8638'__136 v1 v2
du__'8638'__136 :: T_Ctx_6 -> T_Usage_46 -> T_Ctx_6
du__'8638'__136 v0 v1
  = case coe v0 of
      C_'8709'_8 -> coe seq (coe v1) (coe v0)
      C__'44'_'94'__12 v3 v4 v5
        -> case coe v1 of
             C__'8759'__52 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                      -> coe du__'8638'__136 (coe v3) (coe v8)
                    MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
                      -> coe
                           C__'44'_'94'__12 (coe du__'8638'__136 (coe v3) (coe v8)) v4 v5
                    MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
                      -> coe
                           C__'44'_'94'__12 (coe du__'8638'__136 (coe v3) (coe v8)) v4 v5
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Context._≤q'_
d__'8804'q''__162 a0 a1 = ()
data T__'8804'q''__162
  = C_z'8804'z_164 | C_z'8804'o_166 | C_z'8804'm_168 |
    C_o'8804'o_170 | C_o'8804'm_172 | C_m'8804'm_174
-- Once.Lang.Context._⊑ᵘ_
d__'8849''7512'__178 a0 a1 a2 = ()
data T__'8849''7512'__178
  = C_'8849''91''93'_180 |
    C__'8849''8759'__192 T__'8804'q''__162 T__'8849''7512'__178
-- Once.Lang.Context.⊑ᵘ-refl
d_'8849''7512''45'refl_198 ::
  Integer -> T_Usage_46 -> T__'8849''7512'__178
d_'8849''7512''45'refl_198 ~v0 v1 = du_'8849''7512''45'refl_198 v1
du_'8849''7512''45'refl_198 :: T_Usage_46 -> T__'8849''7512'__178
du_'8849''7512''45'refl_198 v0
  = case coe v0 of
      C_'91''93'_48 -> coe C_'8849''91''93'_180
      C__'8759'__52 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
               -> coe
                    C__'8849''8759'__192 (coe C_z'8804'z_164)
                    (coe du_'8849''7512''45'refl_198 (coe v3))
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
               -> coe
                    C__'8849''8759'__192 (coe C_o'8804'o_170)
                    (coe du_'8849''7512''45'refl_198 (coe v3))
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
               -> coe
                    C__'8849''8759'__192 (coe C_m'8804'm_174)
                    (coe du_'8849''7512''45'refl_198 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Context.≤q'-+ˡ
d_'8804'q'''45''43''737'_210 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 -> T__'8804'q''__162
d_'8804'q'''45''43''737'_210 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10 -> coe C_z'8804'z_164
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12 -> coe C_z'8804'o_166
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14 -> coe C_z'8804'm_168
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10 -> coe C_o'8804'o_170
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12 -> coe C_o'8804'm_172
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14 -> coe C_o'8804'm_172
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
        -> coe seq (coe v1) (coe C_m'8804'm_174)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Context.≤q'-+ʳ
d_'8804'q'''45''43''691'_216 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 -> T__'8804'q''__162
d_'8804'q'''45''43''691'_216 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10 -> coe C_z'8804'z_164
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12 -> coe C_o'8804'o_170
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14 -> coe C_m'8804'm_174
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10 -> coe C_z'8804'o_166
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12 -> coe C_o'8804'm_172
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14 -> coe C_m'8804'm_174
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10 -> coe C_z'8804'm_168
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12 -> coe C_o'8804'm_172
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14 -> coe C_m'8804'm_174
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Context.⊑ᵘ-+ˡ
d_'8849''7512''45''43''737'_224 ::
  Integer -> T_Usage_46 -> T_Usage_46 -> T__'8849''7512'__178
d_'8849''7512''45''43''737'_224 ~v0 v1 v2
  = du_'8849''7512''45''43''737'_224 v1 v2
du_'8849''7512''45''43''737'_224 ::
  T_Usage_46 -> T_Usage_46 -> T__'8849''7512'__178
du_'8849''7512''45''43''737'_224 v0 v1
  = case coe v0 of
      C_'91''93'_48 -> coe seq (coe v1) (coe C_'8849''91''93'_180)
      C__'8759'__52 v3 v4
        -> case coe v1 of
             C__'8759'__52 v6 v7
               -> coe
                    C__'8849''8759'__192
                    (d_'8804'q'''45''43''737'_210 (coe v3) (coe v6))
                    (coe du_'8849''7512''45''43''737'_224 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Context.⊑ᵘ-+ʳ
d_'8849''7512''45''43''691'_240 ::
  Integer -> T_Usage_46 -> T_Usage_46 -> T__'8849''7512'__178
d_'8849''7512''45''43''691'_240 ~v0 v1 v2
  = du_'8849''7512''45''43''691'_240 v1 v2
du_'8849''7512''45''43''691'_240 ::
  T_Usage_46 -> T_Usage_46 -> T__'8849''7512'__178
du_'8849''7512''45''43''691'_240 v0 v1
  = case coe v0 of
      C_'91''93'_48 -> coe seq (coe v1) (coe C_'8849''91''93'_180)
      C__'8759'__52 v3 v4
        -> case coe v1 of
             C__'8759'__52 v6 v7
               -> coe
                    C__'8849''8759'__192
                    (d_'8804'q'''45''43''691'_216 (coe v3) (coe v6))
                    (coe du_'8849''7512''45''43''691'_240 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Context.⊑q'-trans
d_'8849'q'''45'trans_256 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  T__'8804'q''__162 -> T__'8804'q''__162 -> T__'8804'q''__162
d_'8849'q'''45'trans_256 ~v0 ~v1 ~v2 v3 v4
  = du_'8849'q'''45'trans_256 v3 v4
du_'8849'q'''45'trans_256 ::
  T__'8804'q''__162 -> T__'8804'q''__162 -> T__'8804'q''__162
du_'8849'q'''45'trans_256 v0 v1
  = case coe v0 of
      C_z'8804'z_164 -> coe v1
      C_z'8804'o_166
        -> case coe v1 of
             C_o'8804'o_170 -> coe v0
             C_o'8804'm_172 -> coe C_z'8804'm_168
             _ -> MAlonzo.RTE.mazUnreachableError
      C_z'8804'm_168 -> coe seq (coe v1) (coe v0)
      C_o'8804'o_170 -> coe v1
      C_o'8804'm_172 -> coe seq (coe v1) (coe v0)
      C_m'8804'm_174 -> coe seq (coe v1) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Context._.z≤-any
d_z'8804''45'any_266 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  T__'8804'q''__162 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  T__'8804'q''__162 -> T__'8804'q''__162
d_z'8804''45'any_266 ~v0 ~v1 ~v2 v3 = du_z'8804''45'any_266 v3
du_z'8804''45'any_266 :: T__'8804'q''__162 -> T__'8804'q''__162
du_z'8804''45'any_266 v0 = coe v0
-- Once.Lang.Context.⊑ᵘ-trans
d_'8849''7512''45'trans_278 ::
  Integer ->
  T_Usage_46 ->
  T_Usage_46 ->
  T_Usage_46 ->
  T__'8849''7512'__178 ->
  T__'8849''7512'__178 -> T__'8849''7512'__178
d_'8849''7512''45'trans_278 ~v0 v1 v2 v3 v4 v5
  = du_'8849''7512''45'trans_278 v1 v2 v3 v4 v5
du_'8849''7512''45'trans_278 ::
  T_Usage_46 ->
  T_Usage_46 ->
  T_Usage_46 ->
  T__'8849''7512'__178 ->
  T__'8849''7512'__178 -> T__'8849''7512'__178
du_'8849''7512''45'trans_278 v0 v1 v2 v3 v4
  = case coe v3 of
      C_'8849''91''93'_180 -> coe seq (coe v4) (coe v3)
      C__'8849''8759'__192 v10 v11
        -> case coe v0 of
             C__'8759'__52 v13 v14
               -> case coe v1 of
                    C__'8759'__52 v16 v17
                      -> case coe v4 of
                           C__'8849''8759'__192 v23 v24
                             -> case coe v2 of
                                  C__'8759'__52 v26 v27
                                    -> coe
                                         C__'8849''8759'__192
                                         (coe du_'8849'q'''45'trans_256 (coe v10) (coe v23))
                                         (coe
                                            du_'8849''7512''45'trans_278 (coe v14) (coe v17)
                                            (coe v27) (coe v11) (coe v24))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Context.⊑ᵘ-*One
d_'8849''7512''45''42'One_292 ::
  Integer -> T_Usage_46 -> T__'8849''7512'__178
d_'8849''7512''45''42'One_292 ~v0 v1
  = du_'8849''7512''45''42'One_292 v1
du_'8849''7512''45''42'One_292 ::
  T_Usage_46 -> T__'8849''7512'__178
du_'8849''7512''45''42'One_292 v0
  = case coe v0 of
      C_'91''93'_48 -> coe C_'8849''91''93'_180
      C__'8759'__52 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
               -> coe
                    C__'8849''8759'__192 (coe C_z'8804'z_164)
                    (coe du_'8849''7512''45''42'One_292 (coe v3))
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
               -> coe
                    C__'8849''8759'__192 (coe C_o'8804'o_170)
                    (coe du_'8849''7512''45''42'One_292 (coe v3))
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
               -> coe
                    C__'8849''8759'__192 (coe C_m'8804'm_174)
                    (coe du_'8849''7512''45''42'One_292 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Context.⊑ᵘ-*Many
d_'8849''7512''45''42'Many_304 ::
  Integer -> T_Usage_46 -> T__'8849''7512'__178
d_'8849''7512''45''42'Many_304 ~v0 v1
  = du_'8849''7512''45''42'Many_304 v1
du_'8849''7512''45''42'Many_304 ::
  T_Usage_46 -> T__'8849''7512'__178
du_'8849''7512''45''42'Many_304 v0
  = case coe v0 of
      C_'91''93'_48 -> coe C_'8849''91''93'_180
      C__'8759'__52 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
               -> coe
                    C__'8849''8759'__192 (coe C_z'8804'z_164)
                    (coe du_'8849''7512''45''42'Many_304 (coe v3))
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
               -> coe
                    C__'8849''8759'__192 (coe C_o'8804'm_172)
                    (coe du_'8849''7512''45''42'Many_304 (coe v3))
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
               -> coe
                    C__'8849''8759'__192 (coe C_m'8804'm_174)
                    (coe du_'8849''7512''45''42'Many_304 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Context.≤q'-⊔ˡ
d_'8804'q'''45''8852''737'_316 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 -> T__'8804'q''__162
d_'8804'q'''45''8852''737'_316 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10 -> coe C_z'8804'z_164
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12 -> coe C_z'8804'o_166
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14 -> coe C_z'8804'm_168
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10 -> coe C_o'8804'o_170
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12 -> coe C_o'8804'o_170
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14 -> coe C_o'8804'm_172
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
        -> coe seq (coe v1) (coe C_m'8804'm_174)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Context.≤q'-⊔ʳ
d_'8804'q'''45''8852''691'_322 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 -> T__'8804'q''__162
d_'8804'q'''45''8852''691'_322 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10 -> coe C_z'8804'z_164
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12 -> coe C_o'8804'o_170
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14 -> coe C_m'8804'm_174
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10 -> coe C_z'8804'o_166
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12 -> coe C_o'8804'o_170
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14 -> coe C_m'8804'm_174
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10 -> coe C_z'8804'm_168
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12 -> coe C_o'8804'm_172
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14 -> coe C_m'8804'm_174
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Context.⊑ᵘ-⊔ˡ
d_'8849''7512''45''8852''737'_330 ::
  Integer -> T_Usage_46 -> T_Usage_46 -> T__'8849''7512'__178
d_'8849''7512''45''8852''737'_330 ~v0 v1 v2
  = du_'8849''7512''45''8852''737'_330 v1 v2
du_'8849''7512''45''8852''737'_330 ::
  T_Usage_46 -> T_Usage_46 -> T__'8849''7512'__178
du_'8849''7512''45''8852''737'_330 v0 v1
  = case coe v0 of
      C_'91''93'_48 -> coe seq (coe v1) (coe C_'8849''91''93'_180)
      C__'8759'__52 v3 v4
        -> case coe v1 of
             C__'8759'__52 v6 v7
               -> coe
                    C__'8849''8759'__192
                    (d_'8804'q'''45''8852''737'_316 (coe v3) (coe v6))
                    (coe du_'8849''7512''45''8852''737'_330 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Context.⊑ᵘ-⊔ʳ
d_'8849''7512''45''8852''691'_346 ::
  Integer -> T_Usage_46 -> T_Usage_46 -> T__'8849''7512'__178
d_'8849''7512''45''8852''691'_346 ~v0 v1 v2
  = du_'8849''7512''45''8852''691'_346 v1 v2
du_'8849''7512''45''8852''691'_346 ::
  T_Usage_46 -> T_Usage_46 -> T__'8849''7512'__178
du_'8849''7512''45''8852''691'_346 v0 v1
  = case coe v0 of
      C_'91''93'_48 -> coe seq (coe v1) (coe C_'8849''91''93'_180)
      C__'8759'__52 v3 v4
        -> case coe v1 of
             C__'8759'__52 v6 v7
               -> coe
                    C__'8849''8759'__192
                    (d_'8804'q'''45''8852''691'_322 (coe v3) (coe v6))
                    (coe du_'8849''7512''45''8852''691'_346 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
