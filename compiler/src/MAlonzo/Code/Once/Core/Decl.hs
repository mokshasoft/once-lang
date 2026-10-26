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

module MAlonzo.Code.Once.Core.Decl where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.Name
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Signature
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type.Concrete

-- Once.Core.Decl.toB
d_toB_6 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Signature.T_BTy_6
d_toB_6 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe MAlonzo.Code.Once.Spec.Signature.C_unit_8
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe MAlonzo.Code.Once.Spec.Signature.C_void_10
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Signature.C__'42'__16 (coe d_toB_6 (coe v1))
             (coe d_toB_6 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Signature.C__'43'__18 (coe d_toB_6 (coe v1))
             (coe d_toB_6 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> coe MAlonzo.Code.Once.Spec.Signature.C_unit_8
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1
        -> coe MAlonzo.Code.Once.Spec.Signature.C_unit_8
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2
        -> coe MAlonzo.Code.Once.Spec.Signature.C_unit_8
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe MAlonzo.Code.Once.Spec.Signature.C_int_12
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe MAlonzo.Code.Once.Spec.Signature.C_float_14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Core.Decl.declS
d_declS_16 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Signature.T_DeclType_106
d_declS_16 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe
             MAlonzo.Code.Once.Spec.Signature.C_constant_108
             (coe d_toB_6 (coe v0))
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe
             MAlonzo.Code.Once.Spec.Signature.C_constant_108
             (coe d_toB_6 (coe v0))
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Signature.C_constant_108
             (coe d_toB_6 (coe v0))
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Signature.C_constant_108
             (coe d_toB_6 (coe v0))
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Once.Spec.Grade.C_fin_42 v6
                      -> case coe v6 of
                           MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                             -> coe
                                  MAlonzo.Code.Once.Spec.Signature.C_value_110
                                  (coe d_toB_6 (coe v1)) (coe v4) (coe d_toB_6 (coe v3))
                           MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                             -> coe
                                  MAlonzo.Code.Once.Spec.Signature.C_operation_112
                                  (coe d_toB_6 (coe v1)) (coe v4) (coe d_toB_6 (coe v3))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Spec.Grade.C_eff_44
                      -> coe
                           MAlonzo.Code.Once.Spec.Signature.C_operation_112
                           (coe d_toB_6 (coe v1)) (coe v4) (coe d_toB_6 (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1
        -> coe
             MAlonzo.Code.Once.Spec.Signature.C_constant_108
             (coe d_toB_6 (coe v0))
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Signature.C_constant_108
             (coe d_toB_6 (coe v0))
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe
             MAlonzo.Code.Once.Spec.Signature.C_constant_108
             (coe d_toB_6 (coe v0))
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             MAlonzo.Code.Once.Spec.Signature.C_constant_108
             (coe d_toB_6 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Core.Decl.⌜toB⌝
d_'8988'toB'8989'_54 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8988'toB'8989'_54 = erased
-- Once.Core.Decl.⌜declS⌝
d_'8988'declS'8989'_68 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Type.Concrete.T_IsConcrete_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8988'declS'8989'_68 = erased
-- Once.Core.Decl.toISig
d_toISig_138 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_toISig_138 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Signature.C__'8758'__124 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Once.Name.d_showCanonical_4 (coe v3))
                       (coe
                          MAlonzo.Code.Once.Spec.Signature.du_'8988'_'8989''7496'_134
                          (coe v4)))
                    (coe d_toISig_138 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Core.Decl.∈-toISig
d_'8712''45'toISig_152 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Signature.T_DeclType_106 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_'8712''45'toISig_152 v0 ~v1 ~v2 v3
  = du_'8712''45'toISig_152 v0 v3
du_'8712''45'toISig_152 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_'8712''45'toISig_152 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> coe
             seq (coe v2)
             (case coe v1 of
                MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v6
                  -> coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased
                MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v6
                  -> coe
                       MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                       (coe du_'8712''45'toISig_152 (coe v3) (coe v6))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Core.Decl.⌜⌝-base
d_'8988''8989''45'base_162 ::
  MAlonzo.Code.Once.Spec.Signature.T_BTy_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
d_'8988''8989''45'base_162 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Signature.C_unit_8
        -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94
      MAlonzo.Code.Once.Spec.Signature.C_void_10
        -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Void_96
      MAlonzo.Code.Once.Spec.Signature.C_int_12
        -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98
      MAlonzo.Code.Once.Spec.Signature.C_float_14
        -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100
      MAlonzo.Code.Once.Spec.Signature.C__'42'__16 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106
             (d_'8988''8989''45'base_162 (coe v1))
             (d_'8988''8989''45'base_162 (coe v2))
      MAlonzo.Code.Once.Spec.Signature.C__'43'__18 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112
             (d_'8988''8989''45'base_162 (coe v1))
             (d_'8988''8989''45'base_162 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Core.Decl.⌜⌝ᵈ-concrete
d_'8988''8989''7496''45'concrete_174 ::
  MAlonzo.Code.Once.Spec.Signature.T_DeclType_106 ->
  MAlonzo.Code.Once.Type.Concrete.T_IsConcrete_6
d_'8988''8989''7496''45'concrete_174 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Signature.C_constant_108 v1
        -> coe
             MAlonzo.Code.Once.Type.Concrete.C_con'45'base_10
             (d_'8988''8989''45'base_162 (coe v1))
      MAlonzo.Code.Once.Spec.Signature.C_value_110 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.Concrete.C_con'45'fun_18
             (d_'8988''8989''45'base_162 (coe v1))
             (d_'8988''8989''45'base_162 (coe v3))
      MAlonzo.Code.Once.Spec.Signature.C_operation_112 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.Concrete.C_con'45'fun_18
             (d_'8988''8989''45'base_162 (coe v1))
             (d_'8988''8989''45'base_162 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Core.Decl.toB-⌜⌝
d_toB'45''8988''8989'_192 ::
  MAlonzo.Code.Once.Spec.Signature.T_BTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toB'45''8988''8989'_192 = erased
-- Once.Core.Decl.declS-⌜⌝ᵈ
d_declS'45''8988''8989''7496'_204 ::
  MAlonzo.Code.Once.Spec.Signature.T_DeclType_106 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_declS'45''8988''8989''7496'_204 = erased
