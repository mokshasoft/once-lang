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

module MAlonzo.Code.Once.Internal.Type.Sub where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Spec.Grade

-- Once.Internal.Type.Sub.·p-diag
d_'183'p'45'diag_10 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
d_'183'p'45'diag_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v1
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pure_52
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'act_58
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'eff_62
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Type.Sub._<:_
d__'60''58'__12 a0 a1 = ()
data T__'60''58'__12
  = C_sub'45'void_16 | C_sub'45'unit_18 | C_sub'45'int_20 |
    C_sub'45'float_22 |
    C_sub'45'arr_38 T__'60''58'__12 T__'60''58'__12
                    MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_sub'45'prod_48 T__'60''58'__12 T__'60''58'__12 |
    C_sub'45'sum_58 T__'60''58'__12 T__'60''58'__12 | C_sub'45'μ_62 |
    C_sub'45'ν_70 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_sub'45'rigid_76
-- Once.Internal.Type.Sub.⊑π-refl
d_'8849'π'45'refl_80 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
d_'8849'π'45'refl_80 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v1
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pure_52
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'act_58
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'eff_62
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Type.Sub.<:-refl
d_'60''58''45'refl_84 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> T__'60''58'__12
d_'60''58''45'refl_84 v0
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Type.C_Unit_20 -> coe C_sub'45'unit_18
      MAlonzo.Code.Once.Internal.Type.C_Void_22 -> coe C_sub'45'void_16
      MAlonzo.Code.Once.Internal.Type.C__'42'__24 v1 v2
        -> coe
             C_sub'45'prod_48 (d_'60''58''45'refl_84 (coe v1))
             (d_'60''58''45'refl_84 (coe v2))
      MAlonzo.Code.Once.Internal.Type.C__'43'__26 v1 v2
        -> coe
             C_sub'45'sum_58 (d_'60''58''45'refl_84 (coe v1))
             (d_'60''58''45'refl_84 (coe v2))
      MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v4 v5
               -> coe
                    C_sub'45'arr_38 (d_'60''58''45'refl_84 (coe v1))
                    (d_'60''58''45'refl_84 (coe v3)) (d_'8849'π'45'refl_80 (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v1
        -> coe C_sub'45'μ_62
      MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v1 v2
        -> coe
             C_sub'45'ν_70
             (d_'8849'π'45'refl_80
                (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v2)))
      MAlonzo.Code.Once.Internal.Type.C_Int_34 -> coe C_sub'45'int_20
      MAlonzo.Code.Once.Internal.Type.C_Float_36 -> coe C_sub'45'float_22
      MAlonzo.Code.Once.Internal.Type.C_rigid_38 v1 v2
        -> coe C_sub'45'rigid_76
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Type.Sub._<:ᶜ_
d__'60''58''7580'__108 a0 a1 = ()
data T__'60''58''7580'__108
  = C_sub'7580''45'void_112 | C_sub'7580''45'unit_114 |
    C_sub'7580''45'int_116 | C_sub'7580''45'float_118 |
    C_sub'7580''45'arr_132 T__'60''58''7580'__108
                           MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_sub'7580''45'prod_142 T__'60''58''7580'__108
                            T__'60''58''7580'__108 |
    C_sub'7580''45'sum_152 T__'60''58''7580'__108
                           T__'60''58''7580'__108 |
    C_sub'7580''45'μ_156 |
    C_sub'7580''45'ν_164 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_sub'7580''45'rigid_170
-- Once.Internal.Type.Sub.<:ᶜ⇒<:
d_'60''58''7580''8658''60''58'_176 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  T__'60''58''7580'__108 -> T__'60''58'__12
d_'60''58''7580''8658''60''58'_176 v0 v1 v2
  = case coe v2 of
      C_sub'7580''45'void_112 -> coe C_sub'45'void_16
      C_sub'7580''45'unit_114 -> coe C_sub'45'unit_18
      C_sub'7580''45'int_116 -> coe C_sub'45'int_20
      C_sub'7580''45'float_118 -> coe C_sub'45'float_22
      C_sub'7580''45'arr_132 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v11 v12 v13
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v14 v15 v16
                      -> coe
                           C_sub'45'arr_38 (d_'60''58''45'refl_84 (coe v11))
                           (d_'60''58''7580''8658''60''58'_176 (coe v13) (coe v16) (coe v9))
                           v10
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_sub'7580''45'prod_142 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Type.C__'42'__24 v11 v12
                      -> coe
                           C_sub'45'prod_48
                           (d_'60''58''7580''8658''60''58'_176 (coe v9) (coe v11) (coe v7))
                           (d_'60''58''7580''8658''60''58'_176 (coe v10) (coe v12) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_sub'7580''45'sum_152 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Type.C__'43'__26 v11 v12
                      -> coe
                           C_sub'45'sum_58
                           (d_'60''58''7580''8658''60''58'_176 (coe v9) (coe v11) (coe v7))
                           (d_'60''58''7580''8658''60''58'_176 (coe v10) (coe v12) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_sub'7580''45'μ_156 -> coe C_sub'45'μ_62
      C_sub'7580''45'ν_164 v6 -> coe C_sub'45'ν_70 v6
      C_sub'7580''45'rigid_170 -> coe C_sub'45'rigid_76
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Type.Sub.<:ᶜ-refl
d_'60''58''7580''45'refl_196 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> T__'60''58''7580'__108
d_'60''58''7580''45'refl_196 v0
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Type.C_Unit_20
        -> coe C_sub'7580''45'unit_114
      MAlonzo.Code.Once.Internal.Type.C_Void_22
        -> coe C_sub'7580''45'void_112
      MAlonzo.Code.Once.Internal.Type.C__'42'__24 v1 v2
        -> coe
             C_sub'7580''45'prod_142 (d_'60''58''7580''45'refl_196 (coe v1))
             (d_'60''58''7580''45'refl_196 (coe v2))
      MAlonzo.Code.Once.Internal.Type.C__'43'__26 v1 v2
        -> coe
             C_sub'7580''45'sum_152 (d_'60''58''7580''45'refl_196 (coe v1))
             (d_'60''58''7580''45'refl_196 (coe v2))
      MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v4 v5
               -> coe
                    C_sub'7580''45'arr_132 (d_'60''58''7580''45'refl_196 (coe v3))
                    (d_'8849'π'45'refl_80 (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v1
        -> coe C_sub'7580''45'μ_156
      MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v1 v2
        -> coe
             C_sub'7580''45'ν_164
             (d_'8849'π'45'refl_80
                (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v2)))
      MAlonzo.Code.Once.Internal.Type.C_Int_34
        -> coe C_sub'7580''45'int_116
      MAlonzo.Code.Once.Internal.Type.C_Float_36
        -> coe C_sub'7580''45'float_118
      MAlonzo.Code.Once.Internal.Type.C_rigid_38 v1 v2
        -> coe C_sub'7580''45'rigid_170
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Type.Sub._⊔_≔_
d__'8852'_'8788'__226 a0 a1 a2 = ()
data T__'8852'_'8788'__226
  = C_constructor_250 T__'60''58''7580'__108 T__'60''58''7580'__108
                      (MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
                       T__'60''58''7580'__108 ->
                       T__'60''58''7580'__108 -> T__'60''58''7580'__108)
-- Once.Internal.Type.Sub._⊔_≔_.left
d_left_242 :: T__'8852'_'8788'__226 -> T__'60''58''7580'__108
d_left_242 v0
  = case coe v0 of
      C_constructor_250 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Type.Sub._⊔_≔_.right
d_right_244 :: T__'8852'_'8788'__226 -> T__'60''58''7580'__108
d_right_244 v0
  = case coe v0 of
      C_constructor_250 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Type.Sub._⊔_≔_.least
d_least_248 ::
  T__'8852'_'8788'__226 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  T__'60''58''7580'__108 ->
  T__'60''58''7580'__108 -> T__'60''58''7580'__108
d_least_248 v0
  = case coe v0 of
      C_constructor_250 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
