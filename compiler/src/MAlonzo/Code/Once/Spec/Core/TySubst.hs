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

module MAlonzo.Code.Once.Spec.Core.TySubst where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Spec.Core.PolyTyping
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.Type.SubLaws

-- Once.Spec.Core.TySubst._._<:ₚ_
d__'60''58''8346'__20 a0 a1 a2 a3 a4 a5 = ()
-- Once.Spec.Core.TySubst.⌈⌉-⟨⟩
d_'8968''8969''45''10216''10217'_514 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8968''8969''45''10216''10217'_514 = erased
-- Once.Spec.Core.TySubst.⌈⌉F-⟨⟩
d_'8968''8969'F'45''10216''10217'_524 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8968''8969'F'45''10216''10217'_524 = erased
-- Once.Spec.Core.TySubst.<:ₚ-refl
d_'60''58''8346''45'refl_598 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'60''58''8346'__602
d_'60''58''8346''45'refl_598 ~v0 ~v1 ~v2 ~v3 v4
  = du_'60''58''8346''45'refl_598 v4
du_'60''58''8346''45'refl_598 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'60''58''8346'__602
du_'60''58''8346''45'refl_598 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_var_24 v1
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'var_608
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_Unit_26
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'unit_614
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_Void_28
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'void_612
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_Int_30
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'int_616
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_Float_32
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'float_618
      MAlonzo.Code.Once.Spec.Core.PolyTy.C__'42'__34 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'prod_650
             (coe du_'60''58''8346''45'refl_598 (coe v1))
             (coe du_'60''58''8346''45'refl_598 (coe v2))
      MAlonzo.Code.Once.Spec.Core.PolyTy.C__'43'__36 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'sum_660
             (coe du_'60''58''8346''45'refl_598 (coe v1))
             (coe du_'60''58''8346''45'refl_598 (coe v2))
      MAlonzo.Code.Once.Spec.Core.PolyTy.C__'8658''91'_'93'__38 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v4 v5
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'arr_640
                    (coe du_'60''58''8346''45'refl_598 (coe v1))
                    (coe du_'60''58''8346''45'refl_598 (coe v3))
                    (MAlonzo.Code.Once.Type.SubLaws.d_'8849'π'45'refl_18 (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_μ'45'type_40 v1
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'μ_664
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_ν'45'type_42 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'ν_672
             (MAlonzo.Code.Once.Type.SubLaws.d_'8849'π'45'refl_18 (coe v2))
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_rigid_44 v1 v2
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'rigid_624
      _ -> MAlonzo.RTE.mazUnreachableError
