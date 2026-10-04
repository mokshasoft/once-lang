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
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Spec.Core.PolyTyping
import qualified MAlonzo.Code.Once.Spec.Core.Syntax
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub

-- Once.Spec.Core.TySubst._._<:ₚ_
d__'60''58''8346'__20 a0 a1 a2 a3 a4 a5 = ()
-- Once.Spec.Core.TySubst._._⊩_⊢[_]_∷_!_
d__'8873'_'8866''91'_'93'_'8759'_'33'__22 a0 a1 a2 a3 a4 a5 a6 a7
                                          a8 a9 a10
  = ()
-- Once.Spec.Core.TySubst._.PCtx
d_PCtx_32 a0 a1 a2 a3 a4 = ()
-- Once.Spec.Core.TySubst._.PTm
d_PTm_34 a0 a1 a2 a3 a4 = ()
-- Once.Spec.Core.TySubst._.lookupP
d_lookupP_62 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PCtx_342 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
d_lookupP_62 ~v0 ~v1 ~v2 = du_lookupP_62
du_lookupP_62 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PCtx_342 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
du_lookupP_62 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Spec.Core.PolyTyping.du_lookupP_366 v2 v3
-- Once.Spec.Core.TySubst.KSub
d_KSub_508 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16) ->
  ()
d_KSub_508 = erased
-- Once.Spec.Core.TySubst.base-⟨⟩
d_base'45''10216''10217'_530 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Base_708) ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Base_708 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Base_708
d_base'45''10216''10217'_530 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
                             v10
  = du_base'45''10216''10217'_530 v8 v9 v10
du_base'45''10216''10217'_530 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Base_708) ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Base_708 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Base_708
du_base'45''10216''10217'_530 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_b'45'var_716
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Core.PolyTy.C_var_24 v5 -> coe v1 v5 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_b'45'Unit_718 -> coe v2
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_b'45'Void_720 -> coe v2
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_b'45'Int_722 -> coe v2
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_b'45'Float_724 -> coe v2
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_b'45'rigid_728
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTy.C_b'45'rigid_728
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_b'45'Prod_734 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Core.PolyTy.C__'42'__34 v7 v8
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C_b'45'Prod_734
                    (coe du_base'45''10216''10217'_530 (coe v7) (coe v1) (coe v5))
                    (coe du_base'45''10216''10217'_530 (coe v8) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_b'45'Sum_740 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Core.PolyTy.C__'43'__36 v7 v8
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C_b'45'Sum_740
                    (coe du_base'45''10216''10217'_530 (coe v7) (coe v1) (coe v5))
                    (coe du_base'45''10216''10217'_530 (coe v8) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.TySubst.wf-⟨⟩
d_wf'45''10216''10217'_572 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Fun_20 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Base_708) ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_WFFun_746 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_WFFun_746
d_wf'45''10216''10217'_572 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
                           v10
  = du_wf'45''10216''10217'_572 v8 v9 v10
du_wf'45''10216''10217'_572 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Fun_20 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Base_708) ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_WFFun_746 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_WFFun_746
du_wf'45''10216''10217'_572 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_wf'45'K_754 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Core.PolyTy.C_K_48 v5
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C_wf'45'K_754
                    (coe du_base'45''10216''10217'_530 (coe v5) (coe v1) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_wf'45'Id_756 -> coe v2
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_wf'45'Sum_762 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Core.PolyTy.C__'8853'__52 v7 v8
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C_wf'45'Sum_762
                    (coe du_wf'45''10216''10217'_572 (coe v7) (coe v1) (coe v5))
                    (coe du_wf'45''10216''10217'_572 (coe v8) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_wf'45'Prod_768 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Core.PolyTy.C__'8855'__54 v7 v8
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C_wf'45'Prod_768
                    (coe du_wf'45''10216''10217'_572 (coe v7) (coe v1) (coe v5))
                    (coe du_wf'45''10216''10217'_572 (coe v8) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.TySubst.⌈⌉-⟨⟩
d_'8968''8969''45''10216''10217'_600 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8968''8969''45''10216''10217'_600 = erased
-- Once.Spec.Core.TySubst.⌈⌉F-⟨⟩
d_'8968''8969'F'45''10216''10217'_610 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8968''8969'F'45''10216''10217'_610 = erased
-- Once.Spec.Core.TySubst.<:ₚ-refl
d_'60''58''8346''45'refl_684 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'60''58''8346'__594
d_'60''58''8346''45'refl_684 ~v0 ~v1 ~v2 ~v3 v4
  = du_'60''58''8346''45'refl_684 v4
du_'60''58''8346''45'refl_684 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'60''58''8346'__594
du_'60''58''8346''45'refl_684 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_var_24 v1
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'var_600
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_Unit_26
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'unit_606
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_Void_28
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'void_604
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_Int_30
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'int_608
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_Float_32
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'float_610
      MAlonzo.Code.Once.Spec.Core.PolyTy.C__'42'__34 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'prod_642
             (coe du_'60''58''8346''45'refl_684 (coe v1))
             (coe du_'60''58''8346''45'refl_684 (coe v2))
      MAlonzo.Code.Once.Spec.Core.PolyTy.C__'43'__36 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'sum_652
             (coe du_'60''58''8346''45'refl_684 (coe v1))
             (coe du_'60''58''8346''45'refl_684 (coe v2))
      MAlonzo.Code.Once.Spec.Core.PolyTy.C__'8658''91'_'93'__38 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v4 v5
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'arr_632
                    (coe du_'60''58''8346''45'refl_684 (coe v1))
                    (coe du_'60''58''8346''45'refl_684 (coe v3))
                    (MAlonzo.Code.Once.Type.Sub.d_'8849'π'45'refl_36 (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_μ'45'type_40 v1
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'μ_656
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_ν'45'type_42 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'ν_664
             (MAlonzo.Code.Once.Type.Sub.d_'8849'π'45'refl_36 (coe v2))
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_rigid_44 v1 v2
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'rigid_616
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.TySubst.<:ₚ-⟨⟩
d_'60''58''8346''45''10216''10217'_724 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'60''58''8346'__594 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'60''58''8346'__594
d_'60''58''8346''45''10216''10217'_724 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
                                       v8
  = du_'60''58''8346''45''10216''10217'_724 v5 v6 v7 v8
du_'60''58''8346''45''10216''10217'_724 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'60''58''8346'__594 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'60''58''8346'__594
du_'60''58''8346''45''10216''10217'_724 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_var_24 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'var_600
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C_var_24 v6
                      -> coe du_'60''58''8346''45'refl_684 (coe v2 v4)
                    _ -> coe v3
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'void_604
               -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'void_604
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'unit_606 -> coe v3
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'int_608 -> coe v3
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'float_610 -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTy.C__'42'__34 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'void_604
               -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'void_604
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'unit_606 -> coe v3
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'int_608 -> coe v3
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'float_610 -> coe v3
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'prod_642 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C__'42'__34 v12 v13
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'prod_642
                           (coe
                              du_'60''58''8346''45''10216''10217'_724 (coe v4) (coe v12) (coe v2)
                              (coe v10))
                           (coe
                              du_'60''58''8346''45''10216''10217'_724 (coe v5) (coe v13) (coe v2)
                              (coe v11))
                    _ -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTy.C__'43'__36 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'void_604
               -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'void_604
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'unit_606 -> coe v3
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'int_608 -> coe v3
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'float_610 -> coe v3
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'sum_652 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C__'43'__36 v12 v13
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'sum_652
                           (coe
                              du_'60''58''8346''45''10216''10217'_724 (coe v4) (coe v12) (coe v2)
                              (coe v10))
                           (coe
                              du_'60''58''8346''45''10216''10217'_724 (coe v5) (coe v13) (coe v2)
                              (coe v11))
                    _ -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTy.C__'8658''91'_'93'__38 v4 v5 v6
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'void_604
               -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'void_604
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'unit_606 -> coe v3
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'int_608 -> coe v3
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'float_610 -> coe v3
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'arr_632 v14 v15 v16
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C__'8658''91'_'93'__38 v17 v18 v19
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'arr_632
                           (coe
                              du_'60''58''8346''45''10216''10217'_724 (coe v17) (coe v4) (coe v2)
                              (coe v14))
                           (coe
                              du_'60''58''8346''45''10216''10217'_724 (coe v6) (coe v19) (coe v2)
                              (coe v15))
                           v16
                    _ -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_μ'45'type_40 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'void_604
               -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'void_604
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'unit_606 -> coe v3
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'int_608 -> coe v3
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'float_610 -> coe v3
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'μ_656
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C_μ'45'type_40 v6
                      -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'μ_656
                    _ -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_ν'45'type_42 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'void_604
               -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'void_604
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'unit_606 -> coe v3
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'int_608 -> coe v3
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'float_610 -> coe v3
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'ν_664 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C_ν'45'type_42 v10 v11
                      -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'ν_664 v9
                    _ -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_rigid_44 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'void_604
               -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'void_604
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'unit_606 -> coe v3
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'int_608 -> coe v3
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'float_610 -> coe v3
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'rigid_616
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C_rigid_44 v8 v9
                      -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'rigid_616
                    _ -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> coe v3
-- Once.Spec.Core.TySubst._⟨_⟩ᶜ
d__'10216'_'10217''7580'_772 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PCtx_342 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PCtx_342
d__'10216'_'10217''7580'_772 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du__'10216'_'10217''7580'_772 v3 v4 v6 v7
du__'10216'_'10217''7580'_772 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PCtx_342 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PCtx_342
du__'10216'_'10217''7580'_772 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8709'_346 -> coe v2
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C__'44'_'94'__350 v5 v6 v7
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C__'44'_'94'__350
             (coe
                du__'10216'_'10217''7580'_772 (coe v0) (coe v1) (coe v5) (coe v3))
             (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10216'_'10217'_88
                (coe v0) (coe v1) (coe v6) (coe v3))
             v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.TySubst.lookup-⟨⟩
d_lookup'45''10216''10217'_796 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PCtx_342 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45''10216''10217'_796 = erased
-- Once.Spec.Core.TySubst._⟨_⟩ₜ
d__'10216'_'10217''8348'_822 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_382 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_382
d__'10216'_'10217''8348'_822 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du__'10216'_'10217''8348'_822 v3 v4 v6 v7
du__'10216'_'10217''8348'_822 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_382 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_382
du__'10216'_'10217''8348'_822 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_var_388 v4 -> coe v2
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_lam_390 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_lam_390
             (coe
                du__'10216'_'10217''8348'_822 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_app_392 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_app_392
             (coe
                du__'10216'_'10217''8348'_822 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_822 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_let'8242'_394 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_let'8242'_394
             (coe
                du__'10216'_'10217''8348'_822 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_822 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_unit_396 -> coe v2
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_pair_398 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_pair_398
             (coe
                du__'10216'_'10217''8348'_822 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_822 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_fst_400 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_fst_400
             (coe
                du__'10216'_'10217''8348'_822 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_snd_402 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_snd_402
             (coe
                du__'10216'_'10217''8348'_822 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_inl_404 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_inl_404
             (coe
                du__'10216'_'10217''8348'_822 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_inr_406 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_inr_406
             (coe
                du__'10216'_'10217''8348'_822 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_case_408 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_case_408
             (coe
                du__'10216'_'10217''8348'_822 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_822 (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10216'_'10217''8348'_822 (coe v0) (coe v1) (coe v6) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_absurd_410 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_absurd_410
             (coe
                du__'10216'_'10217''8348'_822 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_roll_412 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_roll_412
             (coe
                du__'10216'_'10217''8348'_822 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_fold_414 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_fold_414
             (coe
                du__'10216'_'10217''8348'_822 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_822 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_unfold_416 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_unfold_416
             (coe
                du__'10216'_'10217''8348'_822 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_822 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_out_418 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_out_418
             (coe
                du__'10216'_'10217''8348'_822 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_coerce_420 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_coerce_420
             (coe
                MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10216'_'10217'_88 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe
                MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10216'_'10217'_88 (coe v0)
                (coe v1) (coe v5) (coe v3))
             (coe
                du__'10216'_'10217''8348'_822 (coe v0) (coe v1) (coe v6) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_lit_422 v4 -> coe v2
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_prim_424 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_prim_424 (coe v4)
             (coe
                du__'10216'_'10217''8348'_822 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sigop_426 v4 v5 -> coe v2
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_ref_430 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_ref_430 (coe v4)
             (coe
                (\ v6 ->
                   MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10216'_'10217'_88
                     (coe v0) (coe v1) (coe v5 v6) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.TySubst.tsubst
d_tsubst_954 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PCtx_342 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_382 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Base_708) ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__722 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__722
d_tsubst_954 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 v12 v13
             v14 v15
  = du_tsubst_954 v3 v4 v10 v11 v12 v13 v14 v15
du_tsubst_954 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_382 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Base_708) ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__722 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__722
du_tsubst_954 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'var_734
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'var_734
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'lam_754 v12 v18
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_lam_390 v19
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C__'8658''91'_'93'__38 v20 v21 v22
                      -> case coe v21 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v23 v24
                             -> coe
                                  MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'lam_754 v12
                                  (coe
                                     du_tsubst_954 (coe v0) (coe v1) (coe v19) (coe v22) (coe v24)
                                     (coe v5) (coe v6) (coe v18))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'app_776 v10 v11 v12 v14 v18 v19
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_app_392 v20 v21
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'app_776 v10 v11 v12
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10216'_'10217'_88
                       (coe v0) (coe v1) (coe v14) (coe v5))
                    (coe
                       du_tsubst_954 (coe v0) (coe v1) (coe v20)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.PolyTy.C__'8658''91'_'93'__38 (coe v14)
                          (coe MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v12) (coe v4))
                          (coe v3))
                       (coe v4) (coe v5) (coe v6) (coe v18))
                    (coe
                       du_tsubst_954 (coe v0) (coe v1) (coe v21) (coe v14) (coe v4)
                       (coe v5) (coe v6) (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'let_798 v10 v11 v12 v14 v18 v19
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_let'8242'_394 v20 v21
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'let_798 v10 v11 v12
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10216'_'10217'_88
                       (coe v0) (coe v1) (coe v14) (coe v5))
                    (coe
                       du_tsubst_954 (coe v0) (coe v1) (coe v20) (coe v14) (coe v4)
                       (coe v5) (coe v6) (coe v18))
                    (coe
                       du_tsubst_954 (coe v0) (coe v1) (coe v21) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'unit_804
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'unit_804
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'pair_824 v10 v11 v17 v18
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_pair_398 v19 v20
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C__'42'__34 v21 v22
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'pair_824 v10 v11
                           (coe
                              du_tsubst_954 (coe v0) (coe v1) (coe v19) (coe v21) (coe v4)
                              (coe v5) (coe v6) (coe v17))
                           (coe
                              du_tsubst_954 (coe v0) (coe v1) (coe v20) (coe v22) (coe v4)
                              (coe v5) (coe v6) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'fst_840 v13 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_fst_400 v16
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'fst_840
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10216'_'10217'_88
                       (coe v0) (coe v1) (coe v13) (coe v5))
                    (coe
                       du_tsubst_954 (coe v0) (coe v1) (coe v16)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.PolyTy.C__'42'__34 (coe v3) (coe v13))
                       (coe v4) (coe v5) (coe v6) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'snd_856 v12 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_snd_402 v16
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'snd_856
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10216'_'10217'_88
                       (coe v0) (coe v1) (coe v12) (coe v5))
                    (coe
                       du_tsubst_954 (coe v0) (coe v1) (coe v16)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.PolyTy.C__'42'__34 (coe v12) (coe v3))
                       (coe v4) (coe v5) (coe v6) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'inl_872 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_inl_404 v16
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C__'43'__36 v17 v18
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'inl_872
                           (coe
                              du_tsubst_954 (coe v0) (coe v1) (coe v16) (coe v17) (coe v4)
                              (coe v5) (coe v6) (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'inr_888 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_inr_406 v16
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C__'43'__36 v17 v18
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'inr_888
                           (coe
                              du_tsubst_954 (coe v0) (coe v1) (coe v16) (coe v18) (coe v4)
                              (coe v5) (coe v6) (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'case_918 v10 v11 v12 v13 v14 v16 v17 v22 v23 v24
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_case_408 v25 v26 v27
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'case_918 v10 v11 v12
                    v13 v14
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10216'_'10217'_88
                       (coe v0) (coe v1) (coe v16) (coe v5))
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10216'_'10217'_88
                       (coe v0) (coe v1) (coe v17) (coe v5))
                    (coe
                       du_tsubst_954 (coe v0) (coe v1) (coe v25)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.PolyTy.C__'43'__36 (coe v16) (coe v17))
                       (coe v4) (coe v5) (coe v6) (coe v22))
                    (coe
                       du_tsubst_954 (coe v0) (coe v1) (coe v26) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v23))
                    (coe
                       du_tsubst_954 (coe v0) (coe v1) (coe v27) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v24))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'absurd_932 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_absurd_410 v15
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'absurd_932
                    (coe
                       du_tsubst_954 (coe v0) (coe v1) (coe v15)
                       (coe MAlonzo.Code.Once.Spec.Core.PolyTy.C_Void_28) (coe v4)
                       (coe v5) (coe v6) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'roll_946 v14 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_roll_412 v16
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C_μ'45'type_40 v17
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'roll_946
                           (coe du_wf'45''10216''10217'_572 (coe v17) (coe v6) (coe v14))
                           (coe
                              du_tsubst_954 (coe v0) (coe v1) (coe v16)
                              (coe
                                 MAlonzo.Code.Once.Spec.Core.PolyTy.du_'10214'_'10215'F_58 (coe v17)
                                 (coe v3))
                              (coe v4) (coe v5) (coe v6) (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'fold_966 v10 v11 v13 v17 v18 v19
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_fold_414 v20 v21
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'fold_966 v10 v11
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10216'_'10217'F_94
                       (coe v0) (coe v1) (coe v13) (coe v5))
                    (coe du_wf'45''10216''10217'_572 (coe v13) (coe v6) (coe v17))
                    (coe
                       du_tsubst_954 (coe v0) (coe v1) (coe v20)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.PolyTy.C__'8658''91'_'93'__38
                          (coe
                             MAlonzo.Code.Once.Spec.Core.PolyTy.du_'10214'_'10215'F_58 (coe v13)
                             (coe v3))
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
                          (coe v3))
                       (coe v4) (coe v5) (coe v6) (coe v18))
                    (coe
                       du_tsubst_954 (coe v0) (coe v1) (coe v21)
                       (coe MAlonzo.Code.Once.Spec.Core.PolyTy.C_μ'45'type_40 (coe v13))
                       (coe v4) (coe v5) (coe v6) (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'unfold_988 v10 v11 v15 v18 v19 v20
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_unfold_416 v21 v22
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C_ν'45'type_42 v23 v24
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'unfold_988 v10 v11
                           (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10216'_'10217'_88
                              (coe v0) (coe v1) (coe v15) (coe v5))
                           (coe du_wf'45''10216''10217'_572 (coe v23) (coe v6) (coe v18))
                           (coe
                              du_tsubst_954 (coe v0) (coe v1) (coe v21)
                              (coe
                                 MAlonzo.Code.Once.Spec.Core.PolyTy.C__'8658''91'_'93'__38 (coe v15)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v24))
                                 (coe
                                    MAlonzo.Code.Once.Spec.Core.PolyTy.du_'10214'_'10215'F_58
                                    (coe v23) (coe v15)))
                              (coe v4) (coe v5) (coe v6) (coe v19))
                           (coe
                              du_tsubst_954 (coe v0) (coe v1) (coe v22) (coe v15) (coe v4)
                              (coe v5) (coe v6) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'out_1002 v12 v14 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_out_418 v16
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'out_1002
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10216'_'10217'F_94
                       (coe v0) (coe v1) (coe v12) (coe v5))
                    (coe du_wf'45''10216''10217'_572 (coe v12) (coe v6) (coe v14))
                    (coe
                       du_tsubst_954 (coe v0) (coe v1) (coe v16)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.PolyTy.C_ν'45'type_42 (coe v12)
                          (coe v4))
                       (coe v4) (coe v5) (coe v6) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'coerce_1018 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_coerce_420 v17 v18 v19
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'coerce_1018
                    (coe
                       du_'60''58''8346''45''10216''10217'_724 (coe v17) (coe v3) (coe v5)
                       (coe v15))
                    (coe
                       du_tsubst_954 (coe v0) (coe v1) (coe v19) (coe v17) (coe v4)
                       (coe v5) (coe v6) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'lit'45'int_1026
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'lit'45'int_1026
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'lit'45'float_1034
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'lit'45'float_1034
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'prim_1048 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_prim_424 v15 v16
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'prim_1048
                    (coe
                       du_tsubst_954 (coe v0) (coe v1) (coe v16)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.PolyTy.d_'8968'_'8969'_336 (coe v0)
                          (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_primDom_56 (coe v15)))
                       (coe v4) (coe v5) (coe v6) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'sigop_1060 v12 v13 v14 v15
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'sigop_1060 v12 v13
             v14 v15
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'sub'45'eff_1076 v11 v15 v16
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'sub'45'eff_1076 v11
             v15
             (coe
                du_tsubst_954 (coe v0) (coe v1) (coe v2) (coe v3) (coe v11)
                (coe v5) (coe v6) (coe v16))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'ref_1088 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_ref_430 v13 v14
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'ref_1088
                    (\ v15 v16 ->
                       coe
                         du_base'45''10216''10217'_530 (coe v14 v15) (coe v6)
                         (coe v12 v15 v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
