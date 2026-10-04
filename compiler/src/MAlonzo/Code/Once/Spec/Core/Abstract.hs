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

module MAlonzo.Code.Once.Spec.Core.Abstract where

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
import qualified MAlonzo.Code.Once.Spec.Core.AbsTy
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Spec.Core.PolyTyping
import qualified MAlonzo.Code.Once.Spec.Core.Syntax
import qualified MAlonzo.Code.Once.Spec.Core.TySubst
import qualified MAlonzo.Code.Once.Spec.Core.Typing
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub

-- Once.Spec.Core.Abstract.G.Prim
d_Prim_20 a0 a1 a2 = ()
-- Once.Spec.Core.Abstract.G.Tm
d_Tm_26 a0 a1 a2 a3 = ()
-- Once.Spec.Core.Abstract.G.primCod
d_primCod_100 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Type.T_Type_108
d_primCod_100 ~v0 ~v1 ~v2 = du_primCod_100
du_primCod_100 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Type.T_Type_108
du_primCod_100
  = coe MAlonzo.Code.Once.Spec.Core.Syntax.du_primCod_58
-- Once.Spec.Core.Abstract.G.primDom
d_primDom_102 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Type.T_Type_108
d_primDom_102 ~v0 ~v1 ~v2 = du_primDom_102
du_primDom_102 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Type.T_Type_108
du_primDom_102
  = coe MAlonzo.Code.Once.Spec.Core.Syntax.du_primDom_56
-- Once.Spec.Core.Abstract.GT._⊢[_]_∷_!_
d__'8866''91'_'93'_'8759'_'33'__244 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.Spec.Core.Abstract._._<:ₚ_
d__'60''58''8346'__346 a0 a1 a2 a3 a4 a5 = ()
-- Once.Spec.Core.Abstract._._⊩_⊢[_]_∷_!_
d__'8873'_'8866''91'_'93'_'8759'_'33'__348 a0 a1 a2 a3 a4 a5 a6 a7
                                           a8 a9 a10
  = ()
-- Once.Spec.Core.Abstract._.PCtx
d_PCtx_358 a0 a1 a2 a3 a4 = ()
-- Once.Spec.Core.Abstract._.PTm
d_PTm_360 a0 a1 a2 a3 a4 = ()
-- Once.Spec.Core.Abstract._.lookupP
d_lookupP_388 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PCtx_342 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
d_lookupP_388 ~v0 ~v1 ~v2 = du_lookupP_388
du_lookupP_388 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PCtx_342 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
du_lookupP_388 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Spec.Core.PolyTyping.du_lookupP_366 v2 v3
-- Once.Spec.Core.Abstract.abs-<:
d_abs'45''60''58'_614 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'60''58''8346'__594
d_abs'45''60''58'_614 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_abs'45''60''58'_614 v3 v4 v5 v6 v7
du_abs'45''60''58'_614 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'60''58''8346'__594
du_abs'45''60''58'_614 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Type.Sub.C_sub'45'void_52
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'void_604
      MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_54
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'unit_606
      MAlonzo.Code.Once.Type.Sub.C_sub'45'int_56
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'int_608
      MAlonzo.Code.Once.Type.Sub.C_sub'45'float_58
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'float_610
      MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_74 v12 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v15 v16 v17
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v18 v19 v20
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'arr_632
                           (coe
                              du_abs'45''60''58'_614 (coe v0) (coe v1) (coe v18) (coe v15)
                              (coe v12))
                           (coe
                              du_abs'45''60''58'_614 (coe v0) (coe v1) (coe v17) (coe v20)
                              (coe v13))
                           v14
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Sub.C_sub'45'prod_84 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'42'__124 v11 v12
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'42'__124 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'prod_642
                           (coe
                              du_abs'45''60''58'_614 (coe v0) (coe v1) (coe v11) (coe v13)
                              (coe v9))
                           (coe
                              du_abs'45''60''58'_614 (coe v0) (coe v1) (coe v12) (coe v14)
                              (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Sub.C_sub'45'sum_94 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'43'__126 v11 v12
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'sum_652
                           (coe
                              du_abs'45''60''58'_614 (coe v0) (coe v1) (coe v11) (coe v13)
                              (coe v9))
                           (coe
                              du_abs'45''60''58'_614 (coe v0) (coe v1) (coe v12) (coe v14)
                              (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Sub.C_sub'45'μ_98
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'μ_656
      MAlonzo.Code.Once.Type.Sub.C_sub'45'ν_106 v8
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sub'45'ν_664 v8
      MAlonzo.Code.Once.Type.Sub.C_sub'45'rigid_112
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_rigid_138 v7 v8
               -> coe
                    MAlonzo.Code.Once.Spec.Core.TySubst.du_'60''58''8346''45'refl_684
                    (coe
                       MAlonzo.Code.Once.Spec.Core.AbsTy.d_absRigid_68 (coe v0) (coe v1)
                       (coe v7) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Abstract.SigGround
d_SigGround_656 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 -> ()
d_SigGround_656 = erased
-- Once.Spec.Core.Abstract.absCtx
d_absCtx_666 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PCtx_342
d_absCtx_666 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 = du_absCtx_666 v3 v5 v6
du_absCtx_666 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PCtx_342
du_absCtx_666 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Surface.Context.C_'8709'_8
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8709'_346
      MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C__'44'_'94'__350
             (coe du_absCtx_666 (coe v0) (coe v1) (coe v4))
             (MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82
                (coe v0) (coe v1) (coe v5))
             v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Abstract.absCtx-lookup
d_absCtx'45'lookup_688 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_absCtx'45'lookup_688 = erased
-- Once.Spec.Core.Abstract.absTm
d_absTm_714 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_382
d_absTm_714 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 = du_absTm_714 v3 v5 v6
du_absTm_714 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_382
du_absTm_714 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66 v3
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_var_388 (coe v3)
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_lam_390
             (coe du_absTm_714 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Spec.Core.Syntax.C_app_70 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_app_392
             (coe du_absTm_714 (coe v0) (coe v1) (coe v3))
             (coe du_absTm_714 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_72 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_let'8242'_394
             (coe du_absTm_714 (coe v0) (coe v1) (coe v3))
             (coe du_absTm_714 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Spec.Core.Syntax.C_unit_74
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_unit_396
      MAlonzo.Code.Once.Spec.Core.Syntax.C_pair_76 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_pair_398
             (coe du_absTm_714 (coe v0) (coe v1) (coe v3))
             (coe du_absTm_714 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Spec.Core.Syntax.C_fst_78 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_fst_400
             (coe du_absTm_714 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Spec.Core.Syntax.C_snd_80 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_snd_402
             (coe du_absTm_714 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Spec.Core.Syntax.C_inl_82 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_inl_404
             (coe du_absTm_714 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Spec.Core.Syntax.C_inr_84 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_inr_406
             (coe du_absTm_714 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Spec.Core.Syntax.C_case_86 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_case_408
             (coe du_absTm_714 (coe v0) (coe v1) (coe v3))
             (coe du_absTm_714 (coe v0) (coe v1) (coe v4))
             (coe du_absTm_714 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Once.Spec.Core.Syntax.C_absurd_88 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_absurd_410
             (coe du_absTm_714 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Spec.Core.Syntax.C_roll_90 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_roll_412
             (coe du_absTm_714 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Spec.Core.Syntax.C_fold_92 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_fold_414
             (coe du_absTm_714 (coe v0) (coe v1) (coe v3))
             (coe du_absTm_714 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Spec.Core.Syntax.C_unfold_94 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_unfold_416
             (coe du_absTm_714 (coe v0) (coe v1) (coe v3))
             (coe du_absTm_714 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Spec.Core.Syntax.C_out_96 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_out_418
             (coe du_absTm_714 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Spec.Core.Syntax.C_coerce_98 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_coerce_420
             (coe
                MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                (coe v3))
             (coe
                MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                (coe v4))
             (coe du_absTm_714 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lit_100 v3
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_lit_422 (coe v3)
      MAlonzo.Code.Once.Spec.Core.Syntax.C_prim_102 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_prim_424 (coe v3)
             (coe du_absTm_714 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Spec.Core.Syntax.C_sigop_104 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_sigop_426 (coe v3)
             (coe v4)
      MAlonzo.Code.Once.Spec.Core.Syntax.C_ref_108 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_ref_430 (coe v3)
             (coe
                (\ v5 ->
                   MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82
                     (coe v0) (coe v1) (coe v4 v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Abstract.primDom-abs
d_primDom'45'abs_830 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_primDom'45'abs_830 = erased
-- Once.Spec.Core.Abstract.primCod-abs
d_primCod'45'abs_872 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_primCod'45'abs_872 = erased
-- Once.Spec.Core.Abstract.abs-⊢
d_abs'45''8866'_924 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__722
d_abs'45''8866'_924 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11
                    v12
  = du_abs'45''8866'_924 v3 v4 v9 v10 v11 v12
du_abs'45''8866'_924 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__722
du_abs'45''8866'_924 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'var_734
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272 v10 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68 v17
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v18 v19 v20
                      -> case coe v19 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v21 v22
                             -> coe
                                  MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'lam_754 v10
                                  (coe
                                     du_abs'45''8866'_924 (coe v0) (coe v1) (coe v17) (coe v20)
                                     (coe v22) (coe v16))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294 v8 v9 v10 v12 v16 v17
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_app_70 v18 v19
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'app_776 v8 v9 v10
                    (MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82
                       (coe v0) (coe v1) (coe v12))
                    (coe
                       du_abs'45''8866'_924 (coe v0) (coe v1) (coe v18)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v12)
                          (coe MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v10) (coe v4))
                          (coe v3))
                       (coe v4) (coe v16))
                    (coe
                       du_abs'45''8866'_924 (coe v0) (coe v1) (coe v19) (coe v12) (coe v4)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316 v8 v9 v10 v12 v16 v17
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_72 v18 v19
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'let_798 v8 v9 v10
                    (MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82
                       (coe v0) (coe v1) (coe v12))
                    (coe
                       du_abs'45''8866'_924 (coe v0) (coe v1) (coe v18) (coe v12) (coe v4)
                       (coe v16))
                    (coe
                       du_abs'45''8866'_924 (coe v0) (coe v1) (coe v19) (coe v3) (coe v4)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unit_322
        -> coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'unit_804
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'pair_342 v8 v9 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_pair_76 v17 v18
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'42'__124 v19 v20
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'pair_824 v8 v9
                           (coe
                              du_abs'45''8866'_924 (coe v0) (coe v1) (coe v17) (coe v19) (coe v4)
                              (coe v15))
                           (coe
                              du_abs'45''8866'_924 (coe v0) (coe v1) (coe v18) (coe v20) (coe v4)
                              (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fst_358 v11 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_fst_78 v14
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'fst_840
                    (MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82
                       (coe v0) (coe v1) (coe v11))
                    (coe
                       du_abs'45''8866'_924 (coe v0) (coe v1) (coe v14)
                       (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v3) (coe v11))
                       (coe v4) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'snd_374 v10 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_snd_80 v14
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'snd_856
                    (MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82
                       (coe v0) (coe v1) (coe v10))
                    (coe
                       du_abs'45''8866'_924 (coe v0) (coe v1) (coe v14)
                       (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v10) (coe v3))
                       (coe v4) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inl_390 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_inl_82 v14
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v15 v16
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'inl_872
                           (coe
                              du_abs'45''8866'_924 (coe v0) (coe v1) (coe v14) (coe v15) (coe v4)
                              (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inr_406 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_inr_84 v14
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v15 v16
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'inr_888
                           (coe
                              du_abs'45''8866'_924 (coe v0) (coe v1) (coe v14) (coe v16) (coe v4)
                              (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'case_436 v8 v9 v10 v11 v12 v14 v15 v20 v21 v22
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_case_86 v23 v24 v25
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'case_918 v8 v9 v10
                    v11 v12
                    (MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82
                       (coe v0) (coe v1) (coe v14))
                    (MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82
                       (coe v0) (coe v1) (coe v15))
                    (coe
                       du_abs'45''8866'_924 (coe v0) (coe v1) (coe v23)
                       (coe MAlonzo.Code.Once.Type.C__'43'__126 (coe v14) (coe v15))
                       (coe v4) (coe v20))
                    (coe
                       du_abs'45''8866'_924 (coe v0) (coe v1) (coe v24) (coe v3) (coe v4)
                       (coe v21))
                    (coe
                       du_abs'45''8866'_924 (coe v0) (coe v1) (coe v25) (coe v3) (coe v4)
                       (coe v22))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'absurd_450 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_absurd_88 v13
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'absurd_932
                    (coe
                       du_abs'45''8866'_924 (coe v0) (coe v1) (coe v13)
                       (coe MAlonzo.Code.Once.Type.C_Void_122) (coe v4) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'roll_464 v12 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_roll_90 v14
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_130 v15
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'roll_946
                           (MAlonzo.Code.Once.Spec.Core.AbsTy.d_abs'45'wf_352
                              (coe v0) (coe v1) (coe v15) (coe v12))
                           (coe
                              du_abs'45''8866'_924 (coe v0) (coe v1) (coe v14)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v15) (coe v3))
                              (coe v4) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fold_484 v8 v9 v11 v15 v16 v17
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_fold_92 v18 v19
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'fold_966 v8 v9
                    (MAlonzo.Code.Once.Spec.Core.AbsTy.d_absF_88
                       (coe v0) (coe v1) (coe v11))
                    (MAlonzo.Code.Once.Spec.Core.AbsTy.d_abs'45'wf_352
                       (coe v0) (coe v1) (coe v11) (coe v15))
                    (coe
                       du_abs'45''8866'_924 (coe v0) (coe v1) (coe v18)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                          (coe
                             MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v11) (coe v3))
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
                          (coe v3))
                       (coe v4) (coe v16))
                    (coe
                       du_abs'45''8866'_924 (coe v0) (coe v1) (coe v19)
                       (coe MAlonzo.Code.Once.Type.C_μ'45'type_130 (coe v11)) (coe v4)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unfold_506 v8 v9 v13 v16 v17 v18
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_unfold_94 v19 v20
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C_ν'45'type_132 v21 v22
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'unfold_988 v8 v9
                           (MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82
                              (coe v0) (coe v1) (coe v13))
                           (MAlonzo.Code.Once.Spec.Core.AbsTy.d_abs'45'wf_352
                              (coe v0) (coe v1) (coe v21) (coe v16))
                           (coe
                              du_abs'45''8866'_924 (coe v0) (coe v1) (coe v19)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v22))
                                 (coe
                                    MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v21)
                                    (coe v13)))
                              (coe v4) (coe v17))
                           (coe
                              du_abs'45''8866'_924 (coe v0) (coe v1) (coe v20) (coe v13) (coe v4)
                              (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'out_520 v10 v12 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_out_96 v14
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'out_1002
                    (MAlonzo.Code.Once.Spec.Core.AbsTy.d_absF_88
                       (coe v0) (coe v1) (coe v10))
                    (MAlonzo.Code.Once.Spec.Core.AbsTy.d_abs'45'wf_352
                       (coe v0) (coe v1) (coe v10) (coe v12))
                    (coe
                       du_abs'45''8866'_924 (coe v0) (coe v1) (coe v14)
                       (coe MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v10) (coe v4))
                       (coe v4) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'coerce_536 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_coerce_98 v15 v16 v17
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'coerce_1018
                    (coe
                       du_abs'45''60''58'_614 (coe v0) (coe v1) (coe v15) (coe v3)
                       (coe v13))
                    (coe
                       du_abs'45''8866'_924 (coe v0) (coe v1) (coe v17) (coe v15) (coe v4)
                       (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lit'45'int_544
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'lit'45'int_1026
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lit'45'float_552
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'lit'45'float_1034
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'prim_566 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_prim_102 v13 v14
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'prim_1048
                    (coe
                       du_abs'45''8866'_924 (coe v0) (coe v1) (coe v14)
                       (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_primDom_56 (coe v13))
                       (coe v4) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sigop_578 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'sigop_1060 v10 v11
             v12 v13
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'ref_588 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_ref_108 v11 v12
               -> coe
                    MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'ref_1088
                    (\ v13 v14 ->
                       MAlonzo.Code.Once.Spec.Core.AbsTy.d_abs'45'base_318
                         (coe v0) (coe v1) (coe v12 v13) (coe v10 v13 v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_604 v9 v13 v14
        -> coe
             MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8866'sub'45'eff_1076 v9
             v13
             (coe
                du_abs'45''8866'_924 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9)
                (coe v14))
      _ -> MAlonzo.RTE.mazUnreachableError
