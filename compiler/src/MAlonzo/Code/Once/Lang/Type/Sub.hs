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

module MAlonzo.Code.Once.Lang.Type.Sub where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade

-- Once.Lang.Type.Sub._⊑π_
d__'8849'π__8 a0 a1 = ()
data T__'8849'π__8
  = C_'8849''45'pure_10 | C_'8849''45'eff_12 | C_'8849''45'pe_14 |
    C_'8849''45'act_16 | C_'8849''45'pa_18 | C_'8849''45'ae_20
-- Once.Lang.Type.Sub.·p-diag
d_'183'p'45'diag_24 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 -> T__'8849'π__8
d_'183'p'45'diag_24 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> coe C_'8849''45'pure_10
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> coe C_'8849''45'act_16
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
        -> coe C_'8849''45'eff_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Sub._<:_
d__'60''58'__26 a0 a1 = ()
data T__'60''58'__26
  = C_sub'45'void_30 | C_sub'45'unit_32 | C_sub'45'int_34 |
    C_sub'45'float_36 |
    C_sub'45'arr_52 T__'60''58'__26 T__'60''58'__26 T__'8849'π__8 |
    C_sub'45'prod_62 T__'60''58'__26 T__'60''58'__26 |
    C_sub'45'sum_72 T__'60''58'__26 T__'60''58'__26 | C_sub'45'μ_76 |
    C_sub'45'ν_84 T__'8849'π__8 | C_sub'45'rigid_90
-- Once.Lang.Type.Sub.⊑π-refl
d_'8849'π'45'refl_94 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 -> T__'8849'π__8
d_'8849'π'45'refl_94 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> coe C_'8849''45'pure_10
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> coe C_'8849''45'act_16
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
        -> coe C_'8849''45'eff_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Sub.<:-refl
d_'60''58''45'refl_98 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> T__'60''58'__26
d_'60''58''45'refl_98 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20 -> coe C_sub'45'unit_32
      MAlonzo.Code.Once.Lang.Type.C_Void_22 -> coe C_sub'45'void_30
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v1 v2
        -> coe
             C_sub'45'prod_62 (d_'60''58''45'refl_98 (coe v1))
             (d_'60''58''45'refl_98 (coe v2))
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v1 v2
        -> coe
             C_sub'45'sum_72 (d_'60''58''45'refl_98 (coe v1))
             (d_'60''58''45'refl_98 (coe v2))
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v4 v5
               -> coe
                    C_sub'45'arr_52 (d_'60''58''45'refl_98 (coe v1))
                    (d_'60''58''45'refl_98 (coe v3)) (d_'8849'π'45'refl_94 (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v1 -> coe C_sub'45'μ_76
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v1 v2
        -> coe
             C_sub'45'ν_84
             (d_'8849'π'45'refl_94
                (coe MAlonzo.Code.Once.Lang.Type.Grade.d_fin_46 (coe v2)))
      MAlonzo.Code.Once.Lang.Type.C_Int_34 -> coe C_sub'45'int_34
      MAlonzo.Code.Once.Lang.Type.C_Float_36 -> coe C_sub'45'float_36
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v1 v2
        -> coe C_sub'45'rigid_90
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Sub._<:ᶜ_
d__'60''58''7580'__122 a0 a1 = ()
data T__'60''58''7580'__122
  = C_sub'7580''45'void_126 | C_sub'7580''45'unit_128 |
    C_sub'7580''45'int_130 | C_sub'7580''45'float_132 |
    C_sub'7580''45'arr_146 T__'60''58''7580'__122 T__'8849'π__8 |
    C_sub'7580''45'prod_156 T__'60''58''7580'__122
                            T__'60''58''7580'__122 |
    C_sub'7580''45'sum_166 T__'60''58''7580'__122
                           T__'60''58''7580'__122 |
    C_sub'7580''45'μ_170 | C_sub'7580''45'ν_178 T__'8849'π__8 |
    C_sub'7580''45'rigid_184
-- Once.Lang.Type.Sub.<:ᶜ⇒<:
d_'60''58''7580''8658''60''58'_190 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  T__'60''58''7580'__122 -> T__'60''58'__26
d_'60''58''7580''8658''60''58'_190 v0 v1 v2
  = case coe v2 of
      C_sub'7580''45'void_126 -> coe C_sub'45'void_30
      C_sub'7580''45'unit_128 -> coe C_sub'45'unit_32
      C_sub'7580''45'int_130 -> coe C_sub'45'int_34
      C_sub'7580''45'float_132 -> coe C_sub'45'float_36
      C_sub'7580''45'arr_146 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v11 v12 v13
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v14 v15 v16
                      -> coe
                           C_sub'45'arr_52 (d_'60''58''45'refl_98 (coe v11))
                           (d_'60''58''7580''8658''60''58'_190 (coe v13) (coe v16) (coe v9))
                           v10
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_sub'7580''45'prod_156 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v11 v12
                      -> coe
                           C_sub'45'prod_62
                           (d_'60''58''7580''8658''60''58'_190 (coe v9) (coe v11) (coe v7))
                           (d_'60''58''7580''8658''60''58'_190 (coe v10) (coe v12) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_sub'7580''45'sum_166 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v11 v12
                      -> coe
                           C_sub'45'sum_72
                           (d_'60''58''7580''8658''60''58'_190 (coe v9) (coe v11) (coe v7))
                           (d_'60''58''7580''8658''60''58'_190 (coe v10) (coe v12) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_sub'7580''45'μ_170 -> coe C_sub'45'μ_76
      C_sub'7580''45'ν_178 v6 -> coe C_sub'45'ν_84 v6
      C_sub'7580''45'rigid_184 -> coe C_sub'45'rigid_90
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Sub.<:ᶜ-refl
d_'60''58''7580''45'refl_210 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> T__'60''58''7580'__122
d_'60''58''7580''45'refl_210 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20
        -> coe C_sub'7580''45'unit_128
      MAlonzo.Code.Once.Lang.Type.C_Void_22
        -> coe C_sub'7580''45'void_126
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v1 v2
        -> coe
             C_sub'7580''45'prod_156 (d_'60''58''7580''45'refl_210 (coe v1))
             (d_'60''58''7580''45'refl_210 (coe v2))
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v1 v2
        -> coe
             C_sub'7580''45'sum_166 (d_'60''58''7580''45'refl_210 (coe v1))
             (d_'60''58''7580''45'refl_210 (coe v2))
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v4 v5
               -> coe
                    C_sub'7580''45'arr_146 (d_'60''58''7580''45'refl_210 (coe v3))
                    (d_'8849'π'45'refl_94 (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v1
        -> coe C_sub'7580''45'μ_170
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v1 v2
        -> coe
             C_sub'7580''45'ν_178
             (d_'8849'π'45'refl_94
                (coe MAlonzo.Code.Once.Lang.Type.Grade.d_fin_46 (coe v2)))
      MAlonzo.Code.Once.Lang.Type.C_Int_34 -> coe C_sub'7580''45'int_130
      MAlonzo.Code.Once.Lang.Type.C_Float_36
        -> coe C_sub'7580''45'float_132
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v1 v2
        -> coe C_sub'7580''45'rigid_184
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Sub._⊔_≔_
d__'8852'_'8788'__240 a0 a1 a2 = ()
data T__'8852'_'8788'__240
  = C_constructor_264 T__'60''58''7580'__122 T__'60''58''7580'__122
                      (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
                       T__'60''58''7580'__122 ->
                       T__'60''58''7580'__122 -> T__'60''58''7580'__122)
-- Once.Lang.Type.Sub._⊔_≔_.left
d_left_256 :: T__'8852'_'8788'__240 -> T__'60''58''7580'__122
d_left_256 v0
  = case coe v0 of
      C_constructor_264 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Sub._⊔_≔_.right
d_right_258 :: T__'8852'_'8788'__240 -> T__'60''58''7580'__122
d_right_258 v0
  = case coe v0 of
      C_constructor_264 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Sub._⊔_≔_.least
d_least_262 ::
  T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  T__'60''58''7580'__122 ->
  T__'60''58''7580'__122 -> T__'60''58''7580'__122
d_least_262 v0
  = case coe v0 of
      C_constructor_264 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
