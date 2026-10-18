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
d__'60''58''8346'__362 a0 a1 a2 a3 a4 a5 = ()
-- Once.Lang.Core.Abstract._._⊩_⊢[_]_∷_!_
d__'8873'_'8866''91'_'93'_'8759'_'33'__364 a0 a1 a2 a3 a4 a5 a6 a7
                                           a8 a9 a10
  = ()
-- Once.Lang.Core.Abstract._.PCtx
d_PCtx_372 a0 a1 a2 a3 a4 = ()
-- Once.Lang.Core.Abstract._.PTm
d_PTm_374 a0 a1 a2 a3 a4 = ()
-- Once.Lang.Core.Abstract._.lookupP
d_lookupP_404 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PCtx_358 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16
d_lookupP_404 ~v0 ~v1 ~v2 = du_lookupP_404
du_lookupP_404 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PCtx_358 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16
du_lookupP_404 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Core.PolyTyping.du_lookupP_382 v2 v3
-- Once.Lang.Core.Abstract.abs-<:
d_abs'45''60''58'_636 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'60''58''8346'__642
d_abs'45''60''58'_636 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_abs'45''60''58'_636 v3 v4 v5 v6 v7
du_abs'45''60''58'_636 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'60''58''8346'__642
du_abs'45''60''58'_636 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'void_30
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'void_652
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'unit_32
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'unit_654
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'int_34
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'int_656
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'float_36
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'float_658
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v12 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v15 v16 v17
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v18 v19 v20
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'arr_680
                           (coe
                              du_abs'45''60''58'_636 (coe v0) (coe v1) (coe v18) (coe v15)
                              (coe v12))
                           (coe
                              du_abs'45''60''58'_636 (coe v0) (coe v1) (coe v17) (coe v20)
                              (coe v13))
                           v14
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'prod_62 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v11 v12
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'prod_690
                           (coe
                              du_abs'45''60''58'_636 (coe v0) (coe v1) (coe v11) (coe v13)
                              (coe v9))
                           (coe
                              du_abs'45''60''58'_636 (coe v0) (coe v1) (coe v12) (coe v14)
                              (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'sum_72 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v11 v12
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'sum_700
                           (coe
                              du_abs'45''60''58'_636 (coe v0) (coe v1) (coe v11) (coe v13)
                              (coe v9))
                           (coe
                              du_abs'45''60''58'_636 (coe v0) (coe v1) (coe v12) (coe v14)
                              (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'μ_76
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'μ_704
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'ν_84 v8
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sub'45'ν_712 v8
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'rigid_90
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C_rigid_38 v7 v8
               -> coe
                    MAlonzo.Code.Once.Lang.Core.TySubst.du_'60''58''8346''45'refl_532
                    (coe
                       MAlonzo.Code.Once.Lang.Core.AbsTy.d_absRigid_68 (coe v0) (coe v1)
                       (coe v7) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Abstract.SigGround
d_SigGround_678 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 -> ()
d_SigGround_678 = erased
-- Once.Lang.Core.Abstract.absCtx
d_absCtx_688 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PCtx_358
d_absCtx_688 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 = du_absCtx_688 v3 v5 v6
du_absCtx_688 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PCtx_358
du_absCtx_688 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Context.C_'8709'_8
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8709'_362
      MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C__'44'_'94'__366
             (coe du_absCtx_688 (coe v0) (coe v1) (coe v4))
             (MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82
                (coe v0) (coe v1) (coe v5))
             v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Abstract.absCtx-lookup
d_absCtx'45'lookup_710 ::
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
d_absCtx'45'lookup_710 = erased
-- Once.Lang.Core.Abstract.absTm
d_absTm_736 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_398
d_absTm_736 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 = du_absTm_736 v3 v5 v6
du_absTm_736 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_398
du_absTm_736 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66 v3
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_var_404 (coe v3)
      MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68 v3 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_lam_406
             (coe
                MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                (coe v3))
             (coe v4) (coe v5) (coe du_absTm_736 (coe v0) (coe v1) (coe v6))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_app_70 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_app_408
             (coe du_absTm_736 (coe v0) (coe v1) (coe v3))
             (coe du_absTm_736 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_let'8242'_72 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_let'8242'_410 (coe v3)
             (coe du_absTm_736 (coe v0) (coe v1) (coe v4))
             (coe du_absTm_736 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_unit_74
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_unit_412
      MAlonzo.Code.Once.Lang.Core.Syntax.C_pair_76 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_pair_414
             (coe du_absTm_736 (coe v0) (coe v1) (coe v3))
             (coe du_absTm_736 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_fst_78 v3
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_fst_416
             (coe du_absTm_736 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_snd_80 v3
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_snd_418
             (coe du_absTm_736 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_inl_82 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_inl_420
             (coe
                MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                (coe v3))
             (coe du_absTm_736 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_inr_84 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_inr_422
             (coe
                MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                (coe v3))
             (coe du_absTm_736 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_case_86 v3 v4 v5 v6 v7
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_case_424 (coe v3) (coe v4)
             (coe du_absTm_736 (coe v0) (coe v1) (coe v5))
             (coe du_absTm_736 (coe v0) (coe v1) (coe v6))
             (coe du_absTm_736 (coe v0) (coe v1) (coe v7))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_absurd_88 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_absurd_426
             (coe
                MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                (coe v3))
             (coe du_absTm_736 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_roll_90 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_roll_428
             (coe
                MAlonzo.Code.Once.Lang.Core.AbsTy.d_absF_88 (coe v0) (coe v1)
                (coe v3))
             (coe du_absTm_736 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_fold_92 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_fold_430
             (coe
                MAlonzo.Code.Once.Lang.Core.AbsTy.d_absF_88 (coe v0) (coe v1)
                (coe v3))
             (coe du_absTm_736 (coe v0) (coe v1) (coe v4))
             (coe du_absTm_736 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_unfold_94 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_unfold_432
             (coe
                MAlonzo.Code.Once.Lang.Core.AbsTy.d_absF_88 (coe v0) (coe v1)
                (coe v3))
             (coe du_absTm_736 (coe v0) (coe v1) (coe v4))
             (coe du_absTm_736 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_iter_96 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_iter_434
             (coe du_absTm_736 (coe v0) (coe v1) (coe v3))
             (coe du_absTm_736 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_out_98 v3
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_out_436
             (coe du_absTm_736 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_coerce_100 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_coerce_438
             (coe
                MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                (coe v3))
             (coe
                MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                (coe v4))
             (coe du_absTm_736 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_lit_102 v3
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_lit_440 (coe v3)
      MAlonzo.Code.Once.Lang.Core.Syntax.C_prim_104 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_prim_442 (coe v3)
             (coe du_absTm_736 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Lang.Core.Syntax.C_sigop_106 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_sigop_444 (coe v3)
             (coe v4)
      MAlonzo.Code.Once.Lang.Core.Syntax.C_ref_110 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_ref_448 (coe v3)
             (coe
                (\ v5 ->
                   MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82
                     (coe v0) (coe v1) (coe v4 v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Abstract.primDom-abs
d_primDom'45'abs_882 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_primDom'45'abs_882 = erased
-- Once.Lang.Core.Abstract.primCod-abs
d_primCod'45'abs_924 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_primCod'45'abs_924 = erased
-- Once.Lang.Core.Abstract.abs-⊢
d_abs'45''8866'_976 ::
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
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__770
d_abs'45''8866'_976 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 v9 v10 ~v11
                    v12
  = du_abs'45''8866'_976 v3 v4 v9 v10 v12
du_abs'45''8866'_976 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__770
du_abs'45''8866'_976 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'var_782
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276 v9 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68 v16 v17 v18 v19
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v20 v21 v22
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'lam_802 v9
                           (coe
                              du_abs'45''8866'_976 (coe v0) (coe v1) (coe v19) (coe v22)
                              (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'app_302 v7 v8 v9 v10 v11 v12 v13 v17 v18
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_app_70 v19 v20
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'app_828 v7 v8 v9 v10
                    v11 v12
                    (MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82
                       (coe v0) (coe v1) (coe v13))
                    (coe
                       du_abs'45''8866'_976 (coe v0) (coe v1) (coe v19)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v13)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 (coe v9)
                             (coe v10))
                          (coe v3))
                       (coe v17))
                    (coe
                       du_abs'45''8866'_976 (coe v0) (coe v1) (coe v20) (coe v13)
                       (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'let_326 v7 v8 v10 v11 v12 v16 v17
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_let'8242'_72 v18 v19 v20
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'let_852 v7 v8 v10
                    v11
                    (MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82
                       (coe v0) (coe v1) (coe v12))
                    (coe
                       du_abs'45''8866'_976 (coe v0) (coe v1) (coe v19) (coe v12)
                       (coe v16))
                    (coe
                       du_abs'45''8866'_976 (coe v0) (coe v1) (coe v20) (coe v3)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'unit_332
        -> coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'unit_858
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'pair_354 v7 v8 v9 v10 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_pair_76 v17 v18
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v19 v20
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'pair_880 v7 v8 v9
                           v10
                           (coe
                              du_abs'45''8866'_976 (coe v0) (coe v1) (coe v17) (coe v19)
                              (coe v15))
                           (coe
                              du_abs'45''8866'_976 (coe v0) (coe v1) (coe v18) (coe v20)
                              (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'fst_370 v10 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_fst_78 v13
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'fst_896
                    (MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82
                       (coe v0) (coe v1) (coe v10))
                    (coe
                       du_abs'45''8866'_976 (coe v0) (coe v1) (coe v13)
                       (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v3) (coe v10))
                       (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'snd_386 v9 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_snd_80 v13
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'snd_912
                    (MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82
                       (coe v0) (coe v1) (coe v9))
                    (coe
                       du_abs'45''8866'_976 (coe v0) (coe v1) (coe v13)
                       (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v9) (coe v3))
                       (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'inl_402 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_inl_82 v13 v14
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v15 v16
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'inl_928
                           (coe
                              du_abs'45''8866'_976 (coe v0) (coe v1) (coe v14) (coe v15)
                              (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'inr_418 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_inr_84 v13 v14
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v15 v16
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'inr_944
                           (coe
                              du_abs'45''8866'_976 (coe v0) (coe v1) (coe v14) (coe v16)
                              (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'case_448 v7 v8 v11 v12 v13 v14 v19 v20 v21
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_case_86 v22 v23 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'case_974 v7 v8 v11
                    v12
                    (MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82
                       (coe v0) (coe v1) (coe v13))
                    (MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82
                       (coe v0) (coe v1) (coe v14))
                    (coe
                       du_abs'45''8866'_976 (coe v0) (coe v1) (coe v24)
                       (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v13) (coe v14))
                       (coe v19))
                    (coe
                       du_abs'45''8866'_976 (coe v0) (coe v1) (coe v25) (coe v3)
                       (coe v20))
                    (coe
                       du_abs'45''8866'_976 (coe v0) (coe v1) (coe v26) (coe v3)
                       (coe v21))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'absurd_462 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_absurd_88 v12 v13
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'absurd_988
                    (coe
                       du_abs'45''8866'_976 (coe v0) (coe v1) (coe v13)
                       (coe MAlonzo.Code.Once.Lang.Type.C_Void_22) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'roll_476 v11 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_roll_90 v13 v14
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'roll_1002
                    (MAlonzo.Code.Once.Lang.Core.AbsTy.d_abs'45'wf_352
                       (coe v0) (coe v1) (coe v13) (coe v11))
                    (coe
                       du_abs'45''8866'_976 (coe v0) (coe v1) (coe v14)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v13)
                          (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v13)))
                       (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'fold_500 v7 v8 v9 v10 v11 v16 v17 v18 v19
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_fold_92 v20 v21 v22
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'fold_1026 v7 v8 v9
                    v10 v11 v16
                    (MAlonzo.Code.Once.Lang.Core.AbsTy.d_abs'45'wf_352
                       (coe v0) (coe v1) (coe v20) (coe v17))
                    (coe
                       du_abs'45''8866'_976 (coe v0) (coe v1) (coe v21)
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
                       du_abs'45''8866'_976 (coe v0) (coe v1) (coe v22)
                       (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v20))
                       (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'unfold_524 v7 v8 v10 v11 v13 v16 v17 v18
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_unfold_94 v19 v20 v21
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v22 v23
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'unfold_1050 v7 v8
                           v10 v11
                           (MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82
                              (coe v0) (coe v1) (coe v13))
                           (MAlonzo.Code.Once.Lang.Core.AbsTy.d_abs'45'wf_352
                              (coe v0) (coe v1) (coe v19) (coe v16))
                           (coe
                              du_abs'45''8866'_976 (coe v0) (coe v1) (coe v20)
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
                              du_abs'45''8866'_976 (coe v0) (coe v1) (coe v21) (coe v13)
                              (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'out_540 v8 v9 v10 v12 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_out_98 v14
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'out_1066 v8 v9
                    (MAlonzo.Code.Once.Lang.Core.AbsTy.d_absF_88
                       (coe v0) (coe v1) (coe v10))
                    (MAlonzo.Code.Once.Lang.Core.AbsTy.d_abs'45'wf_352
                       (coe v0) (coe v1) (coe v10) (coe v12))
                    (coe
                       du_abs'45''8866'_976 (coe v0) (coe v1) (coe v14)
                       (coe MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v10) (coe v8))
                       (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'coerce_556 v12 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_coerce_100 v14 v15 v16
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'coerce_1082
                    (coe
                       du_abs'45''60''58'_636 (coe v0) (coe v1) (coe v14) (coe v3)
                       (coe v12))
                    (coe
                       du_abs'45''8866'_976 (coe v0) (coe v1) (coe v16) (coe v14)
                       (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lit'45'int_564
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'lit'45'int_1090
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lit'45'float_572
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'lit'45'float_1098
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'prim_586 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_prim_104 v12 v13
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'prim_1112
                    (coe
                       du_abs'45''8866'_976 (coe v0) (coe v1) (coe v13)
                       (coe MAlonzo.Code.Once.Lang.Core.Syntax.du_primDom_56 (coe v12))
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sigop_598 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'sigop_1124 v9 v10
             v11 v12
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'ref_608 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_ref_110 v10 v11
               -> coe
                    MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'ref_1168
                    (\ v12 v13 ->
                       MAlonzo.Code.Once.Lang.Core.AbsTy.d_abs'45'base_318
                         (coe v0) (coe v1) (coe v11 v12) (coe v9 v12 v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'use_624 v7 v12 v13
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'sub'45'use_1156 v7
             v12
             (coe
                du_abs'45''8866'_976 (coe v0) (coe v1) (coe v2) (coe v3) (coe v13))
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_640 v8 v12 v13
        -> coe
             MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8866'sub'45'eff_1140 v8
             v12
             (coe
                du_abs'45''8866'_976 (coe v0) (coe v1) (coe v2) (coe v3) (coe v13))
      _ -> MAlonzo.RTE.mazUnreachableError
