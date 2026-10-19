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

module MAlonzo.Code.Once.Lang.Core.TySubst where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Lang.Core.PolyTy
import qualified MAlonzo.Code.Once.Lang.Core.PolyTyping
import qualified MAlonzo.Code.Once.Lang.Core.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Spec.Name

-- Once.Lang.Core.TySubst._._<:ₚ_
d__'60''58''8346'__20 a0 a1 a2 a3 a4 a5 = ()
-- Once.Lang.Core.TySubst._.PCtx
d_PCtx_30 a0 a1 a2 a3 a4 = ()
-- Once.Lang.Core.TySubst._.PTm
d_PTm_32 a0 a1 a2 a3 a4 = ()
-- Once.Lang.Core.TySubst.KSub
d_KSub_522 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16) ->
  ()
d_KSub_522 = erased
-- Once.Lang.Core.TySubst.<:ₚ-refl
d_'60''58''8346''45'refl_536 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'60''58''8346'__646
d_'60''58''8346''45'refl_536 ~v0 ~v1 ~v2 ~v3 v4
  = du_'60''58''8346''45'refl_536 v4
du_'60''58''8346''45'refl_536 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'60''58''8346'__646
du_'60''58''8346''45'refl_536 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_var_24 v1
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'var_652
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_Unit_26
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'unit_658
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_Void_28
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'void_656
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_Int_30
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'int_660
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_Float_32
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'float_662
      MAlonzo.Code.Once.Lang.Core.PolyTy.C__'42'__34 v1 v2
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'prod_694
             (coe du_'60''58''8346''45'refl_536 (coe v1))
             (coe du_'60''58''8346''45'refl_536 (coe v2))
      MAlonzo.Code.Once.Lang.Core.PolyTy.C__'43'__36 v1 v2
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'sum_704
             (coe du_'60''58''8346''45'refl_536 (coe v1))
             (coe du_'60''58''8346''45'refl_536 (coe v2))
      MAlonzo.Code.Once.Lang.Core.PolyTy.C__'8658''91'_'93'__38 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v4 v5
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'arr_684
                    (coe du_'60''58''8346''45'refl_536 (coe v1))
                    (coe du_'60''58''8346''45'refl_536 (coe v3))
                    (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_μ'45'type_40 v1
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'μ_708
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_ν'45'type_42 v1 v2
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'ν_716
             (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94
                (coe MAlonzo.Code.Once.Lang.Type.Grade.d_fin_46 (coe v2)))
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_rigid_44 v1 v2
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'rigid_668
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.TySubst._⟨_⟩ᶜ
d__'10216'_'10217''7580'_572 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PCtx_362 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PCtx_362
d__'10216'_'10217''7580'_572 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du__'10216'_'10217''7580'_572 v3 v4 v6 v7
du__'10216'_'10217''7580'_572 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PCtx_362 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PCtx_362
du__'10216'_'10217''7580'_572 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8709'_366 -> coe v2
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C__'44'_'94'__370 v5 v6 v7
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C__'44'_'94'__370
             (coe
                du__'10216'_'10217''7580'_572 (coe v0) (coe v1) (coe v5) (coe v3))
             (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88
                (coe v0) (coe v1) (coe v6) (coe v3))
             v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.TySubst._⟨_⟩ₜ
d__'10216'_'10217''8348'_590 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_402 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_402
d__'10216'_'10217''8348'_590 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du__'10216'_'10217''8348'_590 v3 v4 v6 v7
du__'10216'_'10217''8348'_590 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_402 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_402
du__'10216'_'10217''8348'_590 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_var_408 v4 -> coe v2
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_lam_410 v4 v5 v6 v7
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_lam_410
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe v5) (coe v6)
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v7) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_app_412 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_app_412
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_let'8242'_414 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_let'8242'_414 (coe v4)
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v6) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_unit_416 -> coe v2
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_pair_418 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_pair_418
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_fst_420 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_fst_420
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_snd_422 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_snd_422
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_inl_424 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_inl_424
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_inr_426 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_inr_426
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_case_428 v4 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_case_428 (coe v4) (coe v5)
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v6) (coe v3))
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v7) (coe v3))
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v8) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_absurd_430 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_absurd_430
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_roll_432 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_roll_432
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'F_94 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_fold_434 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_fold_434
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'F_94 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v6) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_unfold_436 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_unfold_436
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'F_94 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v6) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_iter_438 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_iter_438
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_out_440 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_out_440
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_coerce_442 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_coerce_442
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88 (coe v0)
                (coe v1) (coe v5) (coe v3))
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v6) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_lit_444 v4 -> coe v2
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_prim_446 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_prim_446 (coe v4)
             (coe
                du__'10216'_'10217''8348'_590 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sigop_448 v4 v5 -> coe v2
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_ref_452 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_ref_452 (coe v4)
             (coe
                (\ v6 ->
                   MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88
                     (coe v0) (coe v1) (coe v5 v6) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
