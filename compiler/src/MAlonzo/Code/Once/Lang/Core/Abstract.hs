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

module MAlonzo.Code.Once.Lang.Core.Abstract where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Core.AbsTy
import qualified MAlonzo.Code.Once.Lang.Core.PolyTy
import qualified MAlonzo.Code.Once.Lang.Core.PolyTyping
import qualified MAlonzo.Code.Once.Lang.Core.Syntax
import qualified MAlonzo.Code.Once.Lang.Core.TySubst
import qualified MAlonzo.Code.Once.Lang.Core.Typing
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Name

-- Once.Lang.Core.Abstract.G.Prim
d_Prim_20 a0 a1 a2 = ()
-- Once.Lang.Core.Abstract.G.Tm
d_Tm_26 a0 a1 a2 a3 = ()
-- Once.Lang.Core.Abstract.G.primCod
d_primCod_102 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
d_primCod_102 ~v0 ~v1 ~v2 = du_primCod_102
du_primCod_102 ::
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_primCod_102
  = coe MAlonzo.Code.Once.Lang.Core.Syntax.du_primCod_58
-- Once.Lang.Core.Abstract.G.primDom
d_primDom_104 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
d_primDom_104 ~v0 ~v1 ~v2 = du_primDom_104
du_primDom_104 ::
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_primDom_104
  = coe MAlonzo.Code.Once.Lang.Core.Syntax.du_primDom_56
-- Once.Lang.Core.Abstract.GT._⊢[_]_∷_!_
d__'8866''91'_'93'_'8759'_'33'__248 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.Lang.Core.Abstract._._<:ₚ_
d__'60''58''8346'__370 a0 a1 a2 a3 a4 a5 = ()
-- Once.Lang.Core.Abstract._._⊩_⊢[_]_∷_!_
d__'8873'_'8866''91'_'93'_'8759'_'33'__372 a0 a1 a2 a3 a4 a5 a6 a7
                                           a8 a9 a10
  = ()
-- Once.Lang.Core.Abstract._.PCtx
d_PCtx_380 a0 a1 a2 a3 a4 = ()
-- Once.Lang.Core.Abstract._.PTm
d_PTm_382 a0 a1 a2 a3 a4 = ()
-- Once.Lang.Core.Abstract._.lookupP
d_lookupP_412 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PCtx_366 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16
d_lookupP_412 ~v0 ~v1 ~v2 = du_lookupP_412
du_lookupP_412 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PCtx_366 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16
du_lookupP_412 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Core.PolyTyping.du_lookupP_390 v2 v3
-- Once.Lang.Core.Abstract.abs-<:
d_abs'45''60''58'_652 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'60''58''8346'__650
d_abs'45''60''58'_652 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_abs'45''60''58'_652 v3 v4 v5 v6 v7
du_abs'45''60''58'_652 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'60''58''8346'__650
du_abs'45''60''58'_652 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'void_34
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'void_660
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'unit_36
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'unit_662
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'int_38
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'int_664
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'float_40
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'float_666
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_56 v12 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v15 v16 v17
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v18 v19 v20
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'arr_688
                           (coe
                              du_abs'45''60''58'_652 (coe v0) (coe v1) (coe v18) (coe v15)
                              (coe v12))
                           (coe
                              du_abs'45''60''58'_652 (coe v0) (coe v1) (coe v17) (coe v20)
                              (coe v13))
                           v14
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'prod_66 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v11 v12
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'prod_698
                           (coe
                              du_abs'45''60''58'_652 (coe v0) (coe v1) (coe v11) (coe v13)
                              (coe v9))
                           (coe
                              du_abs'45''60''58'_652 (coe v0) (coe v1) (coe v12) (coe v14)
                              (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'sum_76 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v11 v12
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'sum_708
                           (coe
                              du_abs'45''60''58'_652 (coe v0) (coe v1) (coe v11) (coe v13)
                              (coe v9))
                           (coe
                              du_abs'45''60''58'_652 (coe v0) (coe v1) (coe v12) (coe v14)
                              (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'μ_80
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'μ_712
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'ν_88 v8
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'ν_720 v8
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'rigid_94
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C_rigid_38 v7 v8
               -> coe
                    MAlonzo.Code.Once.Lang.Core.TySubst.du_'60''58''8346''45'refl_540
                    (coe
                       MAlonzo.Code.Once.Lang.Core.AbsTy.d_absRigid_68 (coe v0) (coe v1)
                       (coe v7) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Abstract.SigGround
d_SigGround_694 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 -> ()
d_SigGround_694 = erased
-- Once.Lang.Core.Abstract.absCtx
d_absCtx_704 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PCtx_366
d_absCtx_704 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 = du_absCtx_704 v3 v5 v6
du_absCtx_704 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PCtx_366
du_absCtx_704 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Context.C_'8709'_8
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8709'_370
      MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C__'44'_'94'__374
             (coe du_absCtx_704 (coe v0) (coe v1) (coe v4))
             (MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82
                (coe v0) (coe v1) (coe v5))
             v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Abstract.absCtx-lookup
d_absCtx'45'lookup_726 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_absCtx'45'lookup_726 = erased
-- Once.Lang.Core.Abstract.absTm
d_absTm_752 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_406
d_absTm_752 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 = du_absTm_752 v3 v5 v6
du_absTm_752 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_406
du_absTm_752 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66 v3
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_var_412 (coe v3)
      MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68 v3 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_lam_414
             (coe
                MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                (coe v3))
             (coe v4) (coe v5) (coe du_absTm_752 (coe v0) (coe v1) (coe v6))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_app_70 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_app_416
             (coe du_absTm_752 (coe v0) (coe v1) (coe v3))
             (coe du_absTm_752 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_let'8242'_72 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_let'8242'_418 (coe v3)
             (coe du_absTm_752 (coe v0) (coe v1) (coe v4))
             (coe du_absTm_752 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_unit_74
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_unit_420
      MAlonzo.Code.Once.Lang.Core.Syntax.C_pair_76 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_pair_422
             (coe du_absTm_752 (coe v0) (coe v1) (coe v3))
             (coe du_absTm_752 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_fst_78 v3
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_fst_424
             (coe du_absTm_752 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_snd_80 v3
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_snd_426
             (coe du_absTm_752 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_inl_82 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_inl_428
             (coe
                MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                (coe v3))
             (coe du_absTm_752 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_inr_84 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_inr_430
             (coe
                MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                (coe v3))
             (coe du_absTm_752 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_case_86 v3 v4 v5 v6 v7
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_case_432 (coe v3) (coe v4)
             (coe du_absTm_752 (coe v0) (coe v1) (coe v5))
             (coe du_absTm_752 (coe v0) (coe v1) (coe v6))
             (coe du_absTm_752 (coe v0) (coe v1) (coe v7))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_absurd_88 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_absurd_434
             (coe
                MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                (coe v3))
             (coe du_absTm_752 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_roll_90 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_roll_436
             (coe
                MAlonzo.Code.Once.Lang.Core.AbsTy.d_absF_88 (coe v0) (coe v1)
                (coe v3))
             (coe du_absTm_752 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_fold_92 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_fold_438
             (coe
                MAlonzo.Code.Once.Lang.Core.AbsTy.d_absF_88 (coe v0) (coe v1)
                (coe v3))
             (coe du_absTm_752 (coe v0) (coe v1) (coe v4))
             (coe du_absTm_752 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_unfold_94 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_unfold_440
             (coe
                MAlonzo.Code.Once.Lang.Core.AbsTy.d_absF_88 (coe v0) (coe v1)
                (coe v3))
             (coe du_absTm_752 (coe v0) (coe v1) (coe v4))
             (coe du_absTm_752 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_iter_96 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_iter_442
             (coe du_absTm_752 (coe v0) (coe v1) (coe v3))
             (coe du_absTm_752 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_out_98 v3
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_out_444
             (coe du_absTm_752 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_coerce_100 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_coerce_446
             (coe
                MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                (coe v3))
             (coe
                MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                (coe v4))
             (coe du_absTm_752 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_lit_102 v3
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_lit_448 (coe v3)
      MAlonzo.Code.Once.Lang.Core.Syntax.C_prim_104 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_prim_450 (coe v3)
             (coe du_absTm_752 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_sigop_106 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sigop_452 (coe v3)
             (coe v4)
      MAlonzo.Code.Once.Lang.Core.Syntax.C_ref_110 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_ref_456 (coe v3)
             (coe
                (\ v5 ->
                   MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82
                     (coe v0) (coe v1) (coe v4 v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Abstract.primDom-abs
d_primDom'45'abs_898 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_primDom'45'abs_898 = erased
-- Once.Lang.Core.Abstract.primCod-abs
d_primCod'45'abs_940 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_primCod'45'abs_940 = erased
-- Once.Lang.Core.Abstract.abs-⊢
d_abs'45''8866'_992 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__778
d_abs'45''8866'_992 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 v9 v10 ~v11
                    v12
  = du_abs'45''8866'_992 v3 v4 v9 v10 v12
du_abs'45''8866'_992 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__778
du_abs'45''8866'_992 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'var_790
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276 v9 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68 v16 v17 v18 v19
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v20 v21 v22
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'lam_810 v9
                           (coe
                              du_abs'45''8866'_992 (coe v0) (coe v1) (coe v19) (coe v22)
                              (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'app_302 v7 v8 v9 v10 v11 v12 v13 v17 v18
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_app_70 v19 v20
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'app_836 v7 v8 v9 v10
                    v11 v12
                    (MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82
                       (coe v0) (coe v1) (coe v13))
                    (coe
                       du_abs'45''8866'_992 (coe v0) (coe v1) (coe v19)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v13)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 (coe v9)
                             (coe v10))
                          (coe v3))
                       (coe v17))
                    (coe
                       du_abs'45''8866'_992 (coe v0) (coe v1) (coe v20) (coe v13)
                       (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'let_326 v7 v8 v10 v11 v12 v16 v17
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_let'8242'_72 v18 v19 v20
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'let_860 v7 v8 v10
                    v11
                    (MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82
                       (coe v0) (coe v1) (coe v12))
                    (coe
                       du_abs'45''8866'_992 (coe v0) (coe v1) (coe v19) (coe v12)
                       (coe v16))
                    (coe
                       du_abs'45''8866'_992 (coe v0) (coe v1) (coe v20) (coe v3)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'unit_332
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'unit_866
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'pair_354 v7 v8 v9 v10 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_pair_76 v17 v18
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v19 v20
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'pair_888 v7 v8 v9
                           v10
                           (coe
                              du_abs'45''8866'_992 (coe v0) (coe v1) (coe v17) (coe v19)
                              (coe v15))
                           (coe
                              du_abs'45''8866'_992 (coe v0) (coe v1) (coe v18) (coe v20)
                              (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'fst_370 v10 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_fst_78 v13
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'fst_904
                    (MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82
                       (coe v0) (coe v1) (coe v10))
                    (coe
                       du_abs'45''8866'_992 (coe v0) (coe v1) (coe v13)
                       (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v3) (coe v10))
                       (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'snd_386 v9 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_snd_80 v13
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'snd_920
                    (MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82
                       (coe v0) (coe v1) (coe v9))
                    (coe
                       du_abs'45''8866'_992 (coe v0) (coe v1) (coe v13)
                       (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v9) (coe v3))
                       (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'inl_402 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_inl_82 v13 v14
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v15 v16
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'inl_936
                           (coe
                              du_abs'45''8866'_992 (coe v0) (coe v1) (coe v14) (coe v15)
                              (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'inr_418 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_inr_84 v13 v14
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v15 v16
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'inr_952
                           (coe
                              du_abs'45''8866'_992 (coe v0) (coe v1) (coe v14) (coe v16)
                              (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'case_448 v7 v8 v11 v12 v13 v14 v19 v20 v21
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_case_86 v22 v23 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'case_982 v7 v8 v11
                    v12
                    (MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82
                       (coe v0) (coe v1) (coe v13))
                    (MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82
                       (coe v0) (coe v1) (coe v14))
                    (coe
                       du_abs'45''8866'_992 (coe v0) (coe v1) (coe v24)
                       (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v13) (coe v14))
                       (coe v19))
                    (coe
                       du_abs'45''8866'_992 (coe v0) (coe v1) (coe v25) (coe v3)
                       (coe v20))
                    (coe
                       du_abs'45''8866'_992 (coe v0) (coe v1) (coe v26) (coe v3)
                       (coe v21))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'absurd_462 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_absurd_88 v12 v13
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'absurd_996
                    (coe
                       du_abs'45''8866'_992 (coe v0) (coe v1) (coe v13)
                       (coe MAlonzo.Code.Once.Lang.Type.C_Void_22) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'roll_476 v11 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_roll_90 v13 v14
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'roll_1010
                    (MAlonzo.Code.Once.Lang.Core.AbsTy.d_abs'45'wf_352
                       (coe v0) (coe v1) (coe v13) (coe v11))
                    (coe
                       du_abs'45''8866'_992 (coe v0) (coe v1) (coe v14)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v13)
                          (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v13)))
                       (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'fold_500 v7 v8 v9 v10 v11 v16 v17 v18 v19
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_fold_92 v20 v21 v22
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'fold_1034 v7 v8 v9
                    v10 v11 v16
                    (MAlonzo.Code.Once.Lang.Core.AbsTy.d_abs'45'wf_352
                       (coe v0) (coe v1) (coe v20) (coe v17))
                    (coe
                       du_abs'45''8866'_992 (coe v0) (coe v1) (coe v21)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                          (coe
                             MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v20)
                             (coe v3))
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v9))
                          (coe v3))
                       (coe v18))
                    (coe
                       du_abs'45''8866'_992 (coe v0) (coe v1) (coe v22)
                       (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v20))
                       (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'unfold_524 v7 v8 v10 v11 v13 v16 v17 v18
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_unfold_94 v19 v20 v21
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v22 v23
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'unfold_1058 v7 v8
                           v10 v11
                           (MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82
                              (coe v0) (coe v1) (coe v13))
                           (MAlonzo.Code.Once.Lang.Core.AbsTy.d_abs'45'wf_352
                              (coe v0) (coe v1) (coe v19) (coe v16))
                           (coe
                              du_abs'45''8866'_992 (coe v0) (coe v1) (coe v20)
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v23))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v19)
                                    (coe v13)))
                              (coe v17))
                           (coe
                              du_abs'45''8866'_992 (coe v0) (coe v1) (coe v21) (coe v13)
                              (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'out_540 v8 v9 v10 v12 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_out_98 v14
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'out_1096 v8 v9
                    (MAlonzo.Code.Once.Lang.Core.AbsTy.d_absF_88
                       (coe v0) (coe v1) (coe v10))
                    (MAlonzo.Code.Once.Lang.Core.AbsTy.d_abs'45'wf_352
                       (coe v0) (coe v1) (coe v10) (coe v12))
                    (coe
                       du_abs'45''8866'_992 (coe v0) (coe v1) (coe v14)
                       (coe MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v10) (coe v8))
                       (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'iter_562 v7 v8 v9 v10 v11 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_iter_96 v17 v18
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'iter_1080 v7 v8 v9
                    v10
                    (MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82
                       (coe v0) (coe v1) (coe v11))
                    (coe
                       du_abs'45''8866'_992 (coe v0) (coe v1) (coe v17)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v11)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38))
                                (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v3) (coe v11)))))
                       (coe v15))
                    (coe
                       du_abs'45''8866'_992 (coe v0) (coe v1) (coe v18) (coe v11)
                       (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'coerce_578 v12 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_coerce_100 v14 v15 v16
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'coerce_1112
                    (coe
                       du_abs'45''60''58'_652 (coe v0) (coe v1) (coe v14) (coe v3)
                       (coe v12))
                    (coe
                       du_abs'45''8866'_992 (coe v0) (coe v1) (coe v16) (coe v14)
                       (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lit'45'int_586
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'lit'45'int_1120
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lit'45'float_594
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'lit'45'float_1128
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'prim_608 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_prim_104 v12 v13
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'prim_1142
                    (coe
                       du_abs'45''8866'_992 (coe v0) (coe v1) (coe v13)
                       (coe MAlonzo.Code.Once.Lang.Core.Syntax.du_primDom_56 (coe v12))
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sigop_620 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'sigop_1154 v9 v10
             v11 v12
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sigop'8314'_636 v10 v12 v13 v14 v15 v16
        -> case coe v15 of
             MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45''8658'_98 v20 v21
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'sigop'8314'_1170 v10
                    v12 v13 v14
                    (coe
                       MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45''8658'_98 v20 v21)
                    v16
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'ref_646 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_ref_110 v10 v11
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'ref_1214
                    (\ v12 v13 ->
                       MAlonzo.Code.Once.Lang.Core.AbsTy.d_abs'45'base_318
                         (coe v0) (coe v1) (coe v11 v12) (coe v9 v12 v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'use_662 v7 v12 v13
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'sub'45'use_1202 v7
             v12
             (coe
                du_abs'45''8866'_992 (coe v0) (coe v1) (coe v2) (coe v3) (coe v13))
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678 v8 v12 v13
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'sub'45'eff_1186 v8
             v12
             (coe
                du_abs'45''8866'_992 (coe v0) (coe v1) (coe v2) (coe v3) (coe v13))
      _ -> MAlonzo.RTE.mazUnreachableError
