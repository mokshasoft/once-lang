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
d_KSub_518 ::
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
d_KSub_518 = erased
-- Once.Lang.Core.TySubst.<:ₚ-refl
d_'60''58''8346''45'refl_532 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'60''58''8346'__642
d_'60''58''8346''45'refl_532 ~v0 ~v1 ~v2 ~v3 v4
  = du_'60''58''8346''45'refl_532 v4
du_'60''58''8346''45'refl_532 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'60''58''8346'__642
du_'60''58''8346''45'refl_532 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_var_24 v1
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'var_648
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_Unit_26
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'unit_654
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_Void_28
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'void_652
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_Int_30
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'int_656
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_Float_32
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'float_658
      MAlonzo.Code.Once.Lang.Core.PolyTy.C__'42'__34 v1 v2
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'prod_690
             (coe du_'60''58''8346''45'refl_532 (coe v1))
             (coe du_'60''58''8346''45'refl_532 (coe v2))
      MAlonzo.Code.Once.Lang.Core.PolyTy.C__'43'__36 v1 v2
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'sum_700
             (coe du_'60''58''8346''45'refl_532 (coe v1))
             (coe du_'60''58''8346''45'refl_532 (coe v2))
      MAlonzo.Code.Once.Lang.Core.PolyTy.C__'8658''91'_'93'__38 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v4 v5
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'arr_680
                    (coe du_'60''58''8346''45'refl_532 (coe v1))
                    (coe du_'60''58''8346''45'refl_532 (coe v3))
                    (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_μ'45'type_40 v1
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'μ_704
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_ν'45'type_42 v1 v2
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'ν_712
             (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v2))
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_rigid_44 v1 v2
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'rigid_664
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.TySubst._⟨_⟩ᶜ
d__'10216'_'10217''7580'_568 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PCtx_358 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PCtx_358
d__'10216'_'10217''7580'_568 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du__'10216'_'10217''7580'_568 v3 v4 v6 v7
du__'10216'_'10217''7580'_568 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PCtx_358 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PCtx_358
du__'10216'_'10217''7580'_568 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8709'_362 -> coe v2
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C__'44'_'94'__366 v5 v6 v7
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C__'44'_'94'__366
             (coe
                du__'10216'_'10217''7580'_568 (coe v0) (coe v1) (coe v5) (coe v3))
             (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88
                (coe v0) (coe v1) (coe v6) (coe v3))
             v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.TySubst._⟨_⟩ₜ
d__'10216'_'10217''8348'_586 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_398 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_398
d__'10216'_'10217''8348'_586 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du__'10216'_'10217''8348'_586 v3 v4 v6 v7
du__'10216'_'10217''8348'_586 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_398 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16) ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_398
du__'10216'_'10217''8348'_586 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_var_404 v4 -> coe v2
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_lam_406 v4 v5 v6 v7
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_lam_406
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe v5) (coe v6)
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v7) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_app_408 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_app_408
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_let'8242'_410 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_let'8242'_410 (coe v4)
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v6) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_unit_412 -> coe v2
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_pair_414 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_pair_414
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_fst_416 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_fst_416
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_snd_418 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_snd_418
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_inl_420 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_inl_420
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_inr_422 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_inr_422
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_case_424 v4 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_case_424 (coe v4) (coe v5)
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v6) (coe v3))
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v7) (coe v3))
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v8) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_absurd_426 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_absurd_426
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_roll_428 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_roll_428
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'F_94 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_fold_430 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_fold_430
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'F_94 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v6) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_unfold_432 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_unfold_432
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'F_94 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v6) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_iter_434 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_iter_434
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_out_436 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_out_436
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_coerce_438 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_coerce_438
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88 (coe v0)
                (coe v1) (coe v4) (coe v3))
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88 (coe v0)
                (coe v1) (coe v5) (coe v3))
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v6) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_lit_440 v4 -> coe v2
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_prim_442 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_prim_442 (coe v4)
             (coe
                du__'10216'_'10217''8348'_586 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sigop_444 v4 v5 -> coe v2
      MAlonzo.Code.Once.Lang.Core.PolyTyping.C_ref_448 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_ref_448 (coe v4)
             (coe
                (\ v6 ->
                   MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10216'_'10217'_88
                     (coe v0) (coe v1) (coe v5 v6) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
