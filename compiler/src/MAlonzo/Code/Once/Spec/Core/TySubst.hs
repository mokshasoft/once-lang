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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Metatheory.SubLaws
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Spec.Core.PolyTyping
import qualified MAlonzo.Code.Once.Spec.Core.Syntax
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Type.Grade
import qualified MAlonzo.Code.Once.Spec.Type.Sub

-- Once.Spec.Core.TySubst._._<:ₚ_
d__'60''58''8346'__20 a0 a1 a2 a3 a4 a5 = ()
-- Once.Spec.Core.TySubst._.PCtx
d_PCtx_30 a0 a1 a2 a3 a4 = ()
-- Once.Spec.Core.TySubst._.PTm
d_PTm_32 a0 a1 a2 a3 a4 = ()
-- Once.Spec.Core.TySubst.KSub
d_KSub_510 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16) ->
  ()
d_KSub_510 = erased
-- Once.Spec.Core.TySubst.<:ₚ-refl
d_'60''58''8346''45'refl_524 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'60''58''8346'__602
d_'60''58''8346''45'refl_524 ~v0 ~v1 ~v2 ~v3 v4
  = du_'60''58''8346''45'refl_524 v4
du_'60''58''8346''45'refl_524 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'60''58''8346'__602
du_'60''58''8346''45'refl_524 v0
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
             (coe du_'60''58''8346''45'refl_524 (coe v1))
             (coe du_'60''58''8346''45'refl_524 (coe v2))
      MAlonzo.Code.Once.Spec.Core.PolyTy.C__'43'__36 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'sum_660
             (coe du_'60''58''8346''45'refl_524 (coe v1))
             (coe du_'60''58''8346''45'refl_524 (coe v2))
      MAlonzo.Code.Once.Spec.Core.PolyTy.C__'8658''91'_'93'__38 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48 v4 v5
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'arr_640
                    (coe du_'60''58''8346''45'refl_524 (coe v1))
                    (coe du_'60''58''8346''45'refl_524 (coe v3))
                    (MAlonzo.Code.Once.Metatheory.SubLaws.d_'8849'π'45'refl_18
                       (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_μ'45'type_40 v1
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'μ_664
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_ν'45'type_42 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'ν_672
             (MAlonzo.Code.Once.Metatheory.SubLaws.d_'8849'π'45'refl_18
                (coe v2))
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_rigid_44 v1 v2
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'rigid_624
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.TySubst._⟨_⟩ᶜ
d__'10216'_'10217''7580'_560 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PCtx_350 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PCtx_350
d__'10216'_'10217''7580'_560 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du__'10216'_'10217''7580'_560 v3 v4 v6 v7
du__'10216'_'10217''7580'_560 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PCtx_350 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PCtx_350
du__'10216'_'10217''7580'_560 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8709'_354 -> coe v2
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C__'44'_'94'__358 v5 v6 v7
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C__'44'_'94'__358
             (coe
                du__'10216'_'10217''7580'_560 (coe v0) (coe v1) (coe v5) (coe v3))
             (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10216'_'10217'_88
                (coe v0) (coe v1) (coe v6) (coe v3))
             v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.TySubst._⟨_⟩ₜ
d__'10216'_'10217''8348'_578 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_390 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_390
d__'10216'_'10217''8348'_578 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du__'10216'_'10217''8348'_578 v3 v4 v6 v7
du__'10216'_'10217''8348'_578 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_390 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_390
du__'10216'_'10217''8348'_578 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_var_396 v4 -> coe v2
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_lam_398 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_lam_398
             (coe
                du__'10216'_'10217''8348'_578 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_app_400 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_app_400
             (coe
                du__'10216'_'10217''8348'_578 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_578 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_let'8242'_402 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_let'8242'_402
             (coe
                du__'10216'_'10217''8348'_578 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_578 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_unit_404 -> coe v2
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_pair_406 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_pair_406
             (coe
                du__'10216'_'10217''8348'_578 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_578 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_fst_408 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_fst_408
             (coe
                du__'10216'_'10217''8348'_578 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_snd_410 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_snd_410
             (coe
                du__'10216'_'10217''8348'_578 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_inl_412 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_inl_412
             (coe
                du__'10216'_'10217''8348'_578 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_inr_414 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_inr_414
             (coe
                du__'10216'_'10217''8348'_578 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_case_416 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_case_416
             (coe
                du__'10216'_'10217''8348'_578 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_578 (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10216'_'10217''8348'_578 (coe v0) (coe v1) (coe v6) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_absurd_418 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_absurd_418
             (coe
                du__'10216'_'10217''8348'_578 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_roll_420 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_roll_420
             (coe
                du__'10216'_'10217''8348'_578 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_fold_422 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_fold_422
             (coe
                du__'10216'_'10217''8348'_578 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_578 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_unfold_424 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_unfold_424
             (coe
                du__'10216'_'10217''8348'_578 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_578 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_out_426 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_out_426
             (coe
                du__'10216'_'10217''8348'_578 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_coerce_428 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_coerce_428
             (coe
                MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10216'_'10217'_88 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe
                MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10216'_'10217'_88 (coe v0)
                (coe v1) (coe v5) (coe v3))
             (coe
                du__'10216'_'10217''8348'_578 (coe v0) (coe v1) (coe v6) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_lit_430 v4 -> coe v2
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_prim_432 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_prim_432 (coe v4)
             (coe
                du__'10216'_'10217''8348'_578 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sigop_434 v4 v5 -> coe v2
      MAlonzo.Code.Once.Spec.Core.PolyTyping.C_ref_438 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_ref_438 (coe v4)
             (coe
                (\ v6 ->
                   MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10216'_'10217'_88
                     (coe v0) (coe v1) (coe v5 v6) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
