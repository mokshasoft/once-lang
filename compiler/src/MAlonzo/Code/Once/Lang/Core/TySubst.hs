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
d_KSub_526 ::
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
d_KSub_526 = erased
-- Once.Lang.Core.TySubst.<:ₚ-refl
d_'60''58''8346''45'refl_540 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'60''58''8346'__650
d_'60''58''8346''45'refl_540 ~v0 ~v1 ~v2 ~v3 v4
  = du_'60''58''8346''45'refl_540 v4
du_'60''58''8346''45'refl_540 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'60''58''8346'__650
du_'60''58''8346''45'refl_540 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_var_24 v1
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'var_656
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_Unit_26
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'unit_662
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_Void_28
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'void_660
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_Int_30
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'int_664
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_Float_32
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'float_666
      MAlonzo.Code.Once.Lang.Core.PolyTy.C__'42'__34 v1 v2
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'prod_698
             (coe du_'60''58''8346''45'refl_540 (coe v1))
             (coe du_'60''58''8346''45'refl_540 (coe v2))
      MAlonzo.Code.Once.Lang.Core.PolyTy.C__'43'__36 v1 v2
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'sum_708
             (coe du_'60''58''8346''45'refl_540 (coe v1))
             (coe du_'60''58''8346''45'refl_540 (coe v2))
      MAlonzo.Code.Once.Lang.Core.PolyTy.C__'8658''91'_'93'__38 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v4 v5
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'arr_688
                    (coe du_'60''58''8346''45'refl_540 (coe v1))
                    (coe du_'60''58''8346''45'refl_540 (coe v3))
                    (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_98 (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_μ'45'type_40 v1
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'μ_712
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_ν'45'type_42 v1 v2
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'ν_720
             (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_98 (coe v2))
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_rigid_44 v1 v2
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'rigid_672
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.TySubst._⟨_⟩ᶜ
d__'10216'_'10217''7580'_576 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PCtx_366 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PCtx_366
d__'10216'_'10217''7580'_576 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du__'10216'_'10217''7580'_576 v3 v4 v6 v7
du__'10216'_'10217''7580'_576 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PCtx_366 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PCtx_366
du__'10216'_'10217''7580'_576 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8709'_370 -> coe v2
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C__'44'_'94'__374 v5 v6 v7
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C__'44'_'94'__374
             (coe
                du__'10216'_'10217''7580'_576 (coe v0) (coe v1) (coe v5) (coe v3))
             (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88
                (coe v0) (coe v1) (coe v6) (coe v3))
             v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.TySubst._⟨_⟩ₜ
d__'10216'_'10217''8348'_594 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_406 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_406
d__'10216'_'10217''8348'_594 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du__'10216'_'10217''8348'_594 v3 v4 v6 v7
du__'10216'_'10217''8348'_594 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_406 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_406
du__'10216'_'10217''8348'_594 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_var_412 v4 -> coe v2
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_lam_414 v4 v5 v6 v7
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_lam_414
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe v5) (coe v6)
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v7) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_app_416 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_app_416
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_let'8242'_418 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_let'8242'_418 (coe v4)
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v6) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_unit_420 -> coe v2
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_pair_422 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_pair_422
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_fst_424 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_fst_424
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_snd_426 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_snd_426
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_inl_428 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_inl_428
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_inr_430 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_inr_430
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_case_432 v4 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_case_432 (coe v4) (coe v5)
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v6) (coe v3))
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v7) (coe v3))
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v8) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_absurd_434 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_absurd_434
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_roll_436 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_roll_436
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'F_94 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_fold_438 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_fold_438
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'F_94 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v6) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_unfold_440 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_unfold_440
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'F_94 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v6) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_iter_442 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_iter_442
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_out_444 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_out_444
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_coerce_446 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_coerce_446
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88 (coe v0)
                (coe v1) (coe v5) (coe v3))
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v6) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_lit_448 v4 -> coe v2
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_prim_450 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_prim_450 (coe v4)
             (coe
                du__'10216'_'10217''8348'_594 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sigop_452 v4 v5 -> coe v2
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_ref_456 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_ref_456 (coe v4)
             (coe
                (\ v6 ->
                   MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88
                     (coe v0) (coe v1) (coe v5 v6) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
