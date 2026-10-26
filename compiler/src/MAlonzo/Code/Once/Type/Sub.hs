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

module MAlonzo.Code.Once.Type.Sub where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Type.Sub.·p-diag
d_'183'p'45'diag_8 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
d_'183'p'45'diag_8 v0
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
-- Once.Type.Sub.⊑π-refl
d_'8849'π'45'refl_12 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
d_'8849'π'45'refl_12 v0
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
-- Once.Type.Sub.pure-⊑
d_pure'45''8849'_16 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
d_pure'45''8849'_16 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v1
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pure_52
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pe_56
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Sub.⊑π-irr
d_'8849'π'45'irr_26 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8849'π'45'irr_26 = erased
-- Once.Type.Sub.<:-refl
d_'60''58''45'refl_32 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8
d_'60''58''45'refl_32 ~v0 v1 = du_'60''58''45'refl_32 v1
du_'60''58''45'refl_32 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8
du_'60''58''45'refl_32 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v1
        -> coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'var_18
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Sub.C_sub'45''42'_50
             (coe du_'60''58''45'refl_32 (coe v1))
             (coe du_'60''58''45'refl_32 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Sub.C_sub'45''43'_60
             (coe du_'60''58''45'refl_32 (coe v1))
             (coe du_'60''58''45'refl_32 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v4 v5
               -> coe
                    MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40
                    (coe du_'60''58''45'refl_32 (coe v1))
                    (coe du_'60''58''45'refl_32 (coe v3))
                    (d_'8849'π'45'refl_12 (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1
        -> coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'μ_64
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Sub.C_sub'45'ν_72
             (d_'8849'π'45'refl_12
                (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v2)))
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Sub.<:ᶜ⇒<:
d_'60''58''7580''8658''60''58'_62 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8
d_'60''58''7580''8658''60''58'_62 ~v0 v1 v2 v3
  = du_'60''58''7580''8658''60''58'_62 v1 v2 v3
du_'60''58''7580''8658''60''58'_62 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8
du_'60''58''7580''8658''60''58'_62 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'void_82
        -> coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'var_86
        -> coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'var_18
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'unit_88
        -> coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'int_90
        -> coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'float_92
        -> coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'arr_106 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v11 v12 v13
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v14 v15 v16
                      -> coe
                           MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40
                           (coe du_'60''58''45'refl_32 (coe v11))
                           (coe
                              du_'60''58''7580''8658''60''58'_62 (coe v13) (coe v16) (coe v9))
                           v10
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''42'_116 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C__'42'__22 v11 v12
                      -> coe
                           MAlonzo.Code.Once.Spec.Sub.C_sub'45''42'_50
                           (coe
                              du_'60''58''7580''8658''60''58'_62 (coe v9) (coe v11) (coe v7))
                           (coe
                              du_'60''58''7580''8658''60''58'_62 (coe v10) (coe v12) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''43'_126 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v11 v12
                      -> coe
                           MAlonzo.Code.Once.Spec.Sub.C_sub'45''43'_60
                           (coe
                              du_'60''58''7580''8658''60''58'_62 (coe v9) (coe v11) (coe v7))
                           (coe
                              du_'60''58''7580''8658''60''58'_62 (coe v10) (coe v12) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'μ_130
        -> coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'μ_64
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'ν_138 v6
        -> coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'ν_72 v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Sub.<:ᶜ-refl
d_'60''58''7580''45'refl_84 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76
d_'60''58''7580''45'refl_84 ~v0 v1
  = du_'60''58''7580''45'refl_84 v1
du_'60''58''7580''45'refl_84 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76
du_'60''58''7580''45'refl_84 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v1
        -> coe MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'var_86
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'unit_88
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'void_82
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''42'_116
             (coe du_'60''58''7580''45'refl_84 (coe v1))
             (coe du_'60''58''7580''45'refl_84 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''43'_126
             (coe du_'60''58''7580''45'refl_84 (coe v1))
             (coe du_'60''58''7580''45'refl_84 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v4 v5
               -> coe
                    MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'arr_106
                    (coe du_'60''58''7580''45'refl_84 (coe v3))
                    (d_'8849'π'45'refl_12 (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1
        -> coe MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'μ_130
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'ν_138
             (d_'8849'π'45'refl_12
                (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v2)))
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'int_90
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'float_92
      _ -> MAlonzo.RTE.mazUnreachableError
