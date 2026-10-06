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

module MAlonzo.Code.Once.Spec.Core.PolyTyping where

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
import qualified MAlonzo.Code.Once.Spec.Core.Syntax
import qualified MAlonzo.Code.Once.Spec.Core.Typing
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub

-- Once.Spec.Core.PolyTyping.G.Lit
d_Lit_18 a0 a1 a2 = ()
-- Once.Spec.Core.PolyTyping.G.Prim
d_Prim_20 a0 a1 a2 = ()
-- Once.Spec.Core.PolyTyping.G.Tm
d_Tm_26 a0 a1 a2 a3 = ()
-- Once.Spec.Core.PolyTyping.G.primCod
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
-- Once.Spec.Core.PolyTyping.G.primDom
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
-- Once.Spec.Core.PolyTyping.GT._⊢[_]_∷_!_
d__'8866''91'_'93'_'8759'_'33'__244 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.Spec.Core.PolyTyping.PCtx
d_PCtx_350 a0 a1 a2 a3 a4 = ()
data T_PCtx_350
  = C_'8709'_354 |
    C__'44'_'94'__358 T_PCtx_350
                      MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
                      MAlonzo.Code.Once.Type.T_Quantity_4
-- Once.Spec.Core.PolyTyping._,_
d__'44'__364 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  T_PCtx_350 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 -> T_PCtx_350
d__'44'__364 ~v0 ~v1 ~v2 v3 v4 = du__'44'__364 v3 v4
du__'44'__364 ::
  T_PCtx_350 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 -> T_PCtx_350
du__'44'__364 v0 v1
  = coe
      C__'44'_'94'__358 v0 v1 (coe MAlonzo.Code.Once.Type.C_Many_10)
-- Once.Spec.Core.PolyTyping.lookupP
d_lookupP_374 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  T_PCtx_350 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
d_lookupP_374 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_lookupP_374 v5 v6
du_lookupP_374 ::
  T_PCtx_350 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
du_lookupP_374 v0 v1
  = case coe v0 of
      C__'44'_'94'__358 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v4
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe du_lookupP_374 (coe v3) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.PolyTyping.PTm
d_PTm_390 a0 a1 a2 a3 a4 = ()
data T_PTm_390
  = C_var_396 MAlonzo.Code.Data.Fin.Base.T_Fin_10 |
    C_lam_398 T_PTm_390 | C_app_400 T_PTm_390 T_PTm_390 |
    C_let'8242'_402 T_PTm_390 T_PTm_390 | C_unit_404 |
    C_pair_406 T_PTm_390 T_PTm_390 | C_fst_408 T_PTm_390 |
    C_snd_410 T_PTm_390 | C_inl_412 T_PTm_390 | C_inr_414 T_PTm_390 |
    C_case_416 T_PTm_390 T_PTm_390 T_PTm_390 | C_absurd_418 T_PTm_390 |
    C_roll_420 T_PTm_390 | C_fold_422 T_PTm_390 T_PTm_390 |
    C_unfold_424 T_PTm_390 T_PTm_390 | C_out_426 T_PTm_390 |
    C_coerce_428 MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
                 MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 T_PTm_390 |
    C_lit_430 MAlonzo.Code.Once.Spec.Core.Syntax.T_Lit_14 |
    C_prim_432 MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 T_PTm_390 |
    C_sigop_434 MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
                MAlonzo.Code.Once.Type.T_Type_108 |
    C_ref_438 MAlonzo.Code.Data.Fin.Base.T_Fin_10
              (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
               MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16)
-- Once.Spec.Core.PolyTyping._⟪_⟫ᶜ
d__'10218'_'10219''7580'_444 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  T_PCtx_350 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6
d__'10218'_'10219''7580'_444 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du__'10218'_'10219''7580'_444 v3 v5 v6
du__'10218'_'10219''7580'_444 ::
  Integer ->
  T_PCtx_350 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6
du__'10218'_'10219''7580'_444 v0 v1 v2
  = case coe v1 of
      C_'8709'_354 -> coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8
      C__'44'_'94'__358 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12
             (coe du__'10218'_'10219''7580'_444 (coe v0) (coe v4) (coe v2))
             (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                (coe v0) (coe v5) (coe v2))
             v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.PolyTyping.lookup-⟪⟫
d_lookup'45''10218''10219'_466 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  T_PCtx_350 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45''10218''10219'_466 = erased
-- Once.Spec.Core.PolyTyping._⟪_⟫ₜ
d__'10218'_'10219''8348'_490 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  T_PTm_390 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d__'10218'_'10219''8348'_490 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du__'10218'_'10219''8348'_490 v3 v5 v6
du__'10218'_'10219''8348'_490 ::
  Integer ->
  T_PTm_390 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du__'10218'_'10219''8348'_490 v0 v1 v2
  = case coe v1 of
      C_var_396 v3
        -> coe MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66 (coe v3)
      C_lam_398 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
             (coe du__'10218'_'10219''8348'_490 (coe v0) (coe v3) (coe v2))
      C_app_400 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_app_70
             (coe du__'10218'_'10219''8348'_490 (coe v0) (coe v3) (coe v2))
             (coe du__'10218'_'10219''8348'_490 (coe v0) (coe v4) (coe v2))
      C_let'8242'_402 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_72
             (coe du__'10218'_'10219''8348'_490 (coe v0) (coe v3) (coe v2))
             (coe du__'10218'_'10219''8348'_490 (coe v0) (coe v4) (coe v2))
      C_unit_404 -> coe MAlonzo.Code.Once.Spec.Core.Syntax.C_unit_74
      C_pair_406 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_pair_76
             (coe du__'10218'_'10219''8348'_490 (coe v0) (coe v3) (coe v2))
             (coe du__'10218'_'10219''8348'_490 (coe v0) (coe v4) (coe v2))
      C_fst_408 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_fst_78
             (coe du__'10218'_'10219''8348'_490 (coe v0) (coe v3) (coe v2))
      C_snd_410 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_snd_80
             (coe du__'10218'_'10219''8348'_490 (coe v0) (coe v3) (coe v2))
      C_inl_412 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_inl_82
             (coe du__'10218'_'10219''8348'_490 (coe v0) (coe v3) (coe v2))
      C_inr_414 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_inr_84
             (coe du__'10218'_'10219''8348'_490 (coe v0) (coe v3) (coe v2))
      C_case_416 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_case_86
             (coe du__'10218'_'10219''8348'_490 (coe v0) (coe v3) (coe v2))
             (coe du__'10218'_'10219''8348'_490 (coe v0) (coe v4) (coe v2))
             (coe du__'10218'_'10219''8348'_490 (coe v0) (coe v5) (coe v2))
      C_absurd_418 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_absurd_88
             (coe du__'10218'_'10219''8348'_490 (coe v0) (coe v3) (coe v2))
      C_roll_420 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_roll_90
             (coe du__'10218'_'10219''8348'_490 (coe v0) (coe v3) (coe v2))
      C_fold_422 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_fold_92
             (coe du__'10218'_'10219''8348'_490 (coe v0) (coe v3) (coe v2))
             (coe du__'10218'_'10219''8348'_490 (coe v0) (coe v4) (coe v2))
      C_unfold_424 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_unfold_94
             (coe du__'10218'_'10219''8348'_490 (coe v0) (coe v3) (coe v2))
             (coe du__'10218'_'10219''8348'_490 (coe v0) (coe v4) (coe v2))
      C_out_426 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_out_96
             (coe du__'10218'_'10219''8348'_490 (coe v0) (coe v3) (coe v2))
      C_coerce_428 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_coerce_98
             (coe
                MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382 (coe v0)
                (coe v3) (coe v2))
             (coe
                MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382 (coe v0)
                (coe v4) (coe v2))
             (coe du__'10218'_'10219''8348'_490 (coe v0) (coe v5) (coe v2))
      C_lit_430 v3
        -> coe MAlonzo.Code.Once.Spec.Core.Syntax.C_lit_100 (coe v3)
      C_prim_432 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_prim_102 (coe v3)
             (coe du__'10218'_'10219''8348'_490 (coe v0) (coe v4) (coe v2))
      C_sigop_434 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_sigop_104 (coe v3) (coe v4)
      C_ref_438 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_ref_108 (coe v3)
             (coe
                (\ v5 ->
                   MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                     (coe v0) (coe v4 v5) (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.PolyTyping._<:ₚ_
d__'60''58''8346'__602 a0 a1 a2 a3 a4 a5 = ()
data T__'60''58''8346'__602
  = C_sub'45'var_608 | C_sub'45'void_612 | C_sub'45'unit_614 |
    C_sub'45'int_616 | C_sub'45'float_618 | C_sub'45'rigid_624 |
    C_sub'45'arr_640 T__'60''58''8346'__602 T__'60''58''8346'__602
                     MAlonzo.Code.Once.Type.Sub.T__'8849'π__6 |
    C_sub'45'prod_650 T__'60''58''8346'__602 T__'60''58''8346'__602 |
    C_sub'45'sum_660 T__'60''58''8346'__602 T__'60''58''8346'__602 |
    C_sub'45'μ_664 |
    C_sub'45'ν_672 MAlonzo.Code.Once.Type.Sub.T__'8849'π__6
-- Once.Spec.Core.PolyTyping.<:ₚ-⟪⟫
d_'60''58''8346''45''10218''10219'_682 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  T__'60''58''8346'__602 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
d_'60''58''8346''45''10218''10219'_682 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_'60''58''8346''45''10218''10219'_682 v4 v5 v6 v7
du_'60''58''8346''45''10218''10219'_682 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  T__'60''58''8346'__602 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
du_'60''58''8346''45''10218''10219'_682 v0 v1 v2 v3
  = let v4
          = case coe v3 of
              C_sub'45'void_612
                -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'void_52
              C_sub'45'unit_614
                -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_54
              C_sub'45'int_616 -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'int_56
              C_sub'45'float_618
                -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'float_58
              _ -> MAlonzo.RTE.mazUnreachableError in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Core.PolyTy.C_var_24 v5
           -> case coe v3 of
                C_sub'45'var_608
                  -> case coe v1 of
                       MAlonzo.Code.Once.Spec.Core.PolyTy.C_var_24 v7
                         -> coe
                              MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170 (coe v2 v5)
                       _ -> coe v4
                C_sub'45'void_612
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'void_52
                C_sub'45'unit_614
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_54
                C_sub'45'int_616 -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'int_56
                C_sub'45'float_618
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'float_58
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Core.PolyTy.C__'42'__34 v5 v6
           -> case coe v3 of
                C_sub'45'void_612
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'void_52
                C_sub'45'unit_614
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_54
                C_sub'45'int_616 -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'int_56
                C_sub'45'float_618
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'float_58
                C_sub'45'prod_650 v11 v12
                  -> case coe v1 of
                       MAlonzo.Code.Once.Spec.Core.PolyTy.C__'42'__34 v13 v14
                         -> coe
                              MAlonzo.Code.Once.Type.Sub.C_sub'45'prod_84
                              (coe
                                 du_'60''58''8346''45''10218''10219'_682 (coe v5) (coe v13) (coe v2)
                                 (coe v11))
                              (coe
                                 du_'60''58''8346''45''10218''10219'_682 (coe v6) (coe v14) (coe v2)
                                 (coe v12))
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Core.PolyTy.C__'43'__36 v5 v6
           -> case coe v3 of
                C_sub'45'void_612
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'void_52
                C_sub'45'unit_614
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_54
                C_sub'45'int_616 -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'int_56
                C_sub'45'float_618
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'float_58
                C_sub'45'sum_660 v11 v12
                  -> case coe v1 of
                       MAlonzo.Code.Once.Spec.Core.PolyTy.C__'43'__36 v13 v14
                         -> coe
                              MAlonzo.Code.Once.Type.Sub.C_sub'45'sum_94
                              (coe
                                 du_'60''58''8346''45''10218''10219'_682 (coe v5) (coe v13) (coe v2)
                                 (coe v11))
                              (coe
                                 du_'60''58''8346''45''10218''10219'_682 (coe v6) (coe v14) (coe v2)
                                 (coe v12))
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Core.PolyTy.C__'8658''91'_'93'__38 v5 v6 v7
           -> case coe v3 of
                C_sub'45'void_612
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'void_52
                C_sub'45'unit_614
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_54
                C_sub'45'int_616 -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'int_56
                C_sub'45'float_618
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'float_58
                C_sub'45'arr_640 v15 v16 v17
                  -> case coe v1 of
                       MAlonzo.Code.Once.Spec.Core.PolyTy.C__'8658''91'_'93'__38 v18 v19 v20
                         -> coe
                              MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_74
                              (coe
                                 du_'60''58''8346''45''10218''10219'_682 (coe v18) (coe v5) (coe v2)
                                 (coe v15))
                              (coe
                                 du_'60''58''8346''45''10218''10219'_682 (coe v7) (coe v20) (coe v2)
                                 (coe v16))
                              v17
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Core.PolyTy.C_μ'45'type_40 v5
           -> case coe v3 of
                C_sub'45'void_612
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'void_52
                C_sub'45'unit_614
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_54
                C_sub'45'int_616 -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'int_56
                C_sub'45'float_618
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'float_58
                C_sub'45'μ_664
                  -> case coe v1 of
                       MAlonzo.Code.Once.Spec.Core.PolyTy.C_μ'45'type_40 v7
                         -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'μ_98
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Core.PolyTy.C_ν'45'type_42 v5 v6
           -> case coe v3 of
                C_sub'45'void_612
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'void_52
                C_sub'45'unit_614
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_54
                C_sub'45'int_616 -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'int_56
                C_sub'45'float_618
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'float_58
                C_sub'45'ν_672 v10
                  -> case coe v1 of
                       MAlonzo.Code.Once.Spec.Core.PolyTy.C_ν'45'type_42 v11 v12
                         -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'ν_106 v10
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Core.PolyTy.C_rigid_44 v5 v6
           -> case coe v3 of
                C_sub'45'void_612
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'void_52
                C_sub'45'unit_614
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_54
                C_sub'45'int_616 -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'int_56
                C_sub'45'float_618
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'float_58
                C_sub'45'rigid_624
                  -> case coe v1 of
                       MAlonzo.Code.Once.Spec.Core.PolyTy.C_rigid_44 v9 v10
                         -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'rigid_112
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v4)
-- Once.Spec.Core.PolyTyping._⊩_⊢[_]_∷_!_
d__'8873'_'8866''91'_'93'_'8759'_'33'__730 a0 a1 a2 a3 a4 a5 a6 a7
                                           a8 a9 a10
  = ()
data T__'8873'_'8866''91'_'93'_'8759'_'33'__730
  = C_'8866'var_742 |
    C_'8866'lam_762 MAlonzo.Code.Once.Type.T_Quantity_4
                    T__'8873'_'8866''91'_'93'_'8759'_'33'__730 |
    C_'8866'app_784 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Type.T_Quantity_4
                    MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
                    T__'8873'_'8866''91'_'93'_'8759'_'33'__730
                    T__'8873'_'8866''91'_'93'_'8759'_'33'__730 |
    C_'8866'let_806 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Type.T_Quantity_4
                    MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
                    T__'8873'_'8866''91'_'93'_'8759'_'33'__730
                    T__'8873'_'8866''91'_'93'_'8759'_'33'__730 |
    C_'8866'unit_812 |
    C_'8866'pair_832 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__730
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__730 |
    C_'8866'fst_848 MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
                    T__'8873'_'8866''91'_'93'_'8759'_'33'__730 |
    C_'8866'snd_864 MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
                    T__'8873'_'8866''91'_'93'_'8759'_'33'__730 |
    C_'8866'inl_880 T__'8873'_'8866''91'_'93'_'8759'_'33'__730 |
    C_'8866'inr_896 T__'8873'_'8866''91'_'93'_'8759'_'33'__730 |
    C_'8866'case_924 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                     MAlonzo.Code.Once.Type.T_Quantity_4
                     MAlonzo.Code.Once.Type.T_Quantity_4
                     MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
                     MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__730
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__730
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__730 |
    C_'8866'absurd_938 T__'8873'_'8866''91'_'93'_'8759'_'33'__730 |
    C_'8866'roll_952 MAlonzo.Code.Once.Spec.Core.PolyTy.T_WFFun_746
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__730 |
    C_'8866'fold_972 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                     MAlonzo.Code.Once.Spec.Core.PolyTy.T_Fun_20
                     MAlonzo.Code.Once.Spec.Core.PolyTy.T_WFFun_746
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__730
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__730 |
    C_'8866'unfold_994 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                       MAlonzo.Code.Once.Surface.Context.T_Usage_60
                       MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
                       MAlonzo.Code.Once.Spec.Core.PolyTy.T_WFFun_746
                       T__'8873'_'8866''91'_'93'_'8759'_'33'__730
                       T__'8873'_'8866''91'_'93'_'8759'_'33'__730 |
    C_'8866'out_1008 MAlonzo.Code.Once.Spec.Core.PolyTy.T_Fun_20
                     MAlonzo.Code.Once.Spec.Core.PolyTy.T_WFFun_746
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__730 |
    C_'8866'coerce_1024 T__'60''58''8346'__602
                        T__'8873'_'8866''91'_'93'_'8759'_'33'__730 |
    C_'8866'lit'45'int_1032 | C_'8866'lit'45'float_1040 |
    C_'8866'prim_1054 T__'8873'_'8866''91'_'93'_'8759'_'33'__730 |
    C_'8866'sigop_1066 MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222
                       AgdaAny MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748
                       MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 |
    C_'8866'sub'45'eff_1082 MAlonzo.Code.Once.Type.T_Purity_32
                            MAlonzo.Code.Once.Type.Sub.T__'8849'π__6
                            T__'8873'_'8866''91'_'93'_'8759'_'33'__730 |
    C_'8866'sub'45'use_1098 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                            MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
                            T__'8873'_'8866''91'_'93'_'8759'_'33'__730 |
    C_'8866'ref_1110 (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
                      MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                      MAlonzo.Code.Once.Spec.Core.PolyTy.T_Base_708)
-- Once.Spec.Core.PolyTyping.,-⟪⟫
d_'44''45''10218''10219'_1122 ::
  T_PCtx_350 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'44''45''10218''10219'_1122 = erased
-- Once.Spec.Core.PolyTyping.instantiate
d_instantiate_1148 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  Integer ->
  T_PCtx_350 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  T_PTm_390 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  T__'8873'_'8866''91'_'93'_'8759'_'33'__730 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_instantiate_1148 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 v12
                   v13
  = du_instantiate_1148 v3 v8 v9 v10 v11 v12 v13
du_instantiate_1148 ::
  Integer ->
  T_PTm_390 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  T__'8873'_'8866''91'_'93'_'8759'_'33'__730 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_instantiate_1148 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      C_'8866'var_742
        -> coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252
      C_'8866'lam_762 v11 v17
        -> case coe v1 of
             C_lam_398 v18
               -> case coe v2 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C__'8658''91'_'93'__38 v19 v20 v21
                      -> case coe v20 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v22 v23
                             -> coe
                                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272 v11
                                  (coe
                                     du_instantiate_1148 (coe v0) (coe v18) (coe v21) (coe v23)
                                     (coe v4) (coe v5) (coe v17))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'app_784 v9 v10 v11 v13 v17 v18
        -> case coe v1 of
             C_app_400 v19 v20
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294 v9 v10 v11
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                       (coe v0) (coe v13) (coe v4))
                    (coe
                       du_instantiate_1148 (coe v0) (coe v19)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.PolyTy.C__'8658''91'_'93'__38 (coe v13)
                          (coe MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v11) (coe v3))
                          (coe v2))
                       (coe v3) (coe v4) (coe v5) (coe v17))
                    (coe
                       du_instantiate_1148 (coe v0) (coe v20) (coe v13) (coe v3) (coe v4)
                       (coe v5) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'let_806 v9 v10 v11 v13 v17 v18
        -> case coe v1 of
             C_let'8242'_402 v19 v20
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316 v9 v10 v11
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                       (coe v0) (coe v13) (coe v4))
                    (coe
                       du_instantiate_1148 (coe v0) (coe v19) (coe v13) (coe v3) (coe v4)
                       (coe v5) (coe v17))
                    (coe
                       du_instantiate_1148 (coe v0) (coe v20) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'unit_812
        -> coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unit_322
      C_'8866'pair_832 v9 v10 v16 v17
        -> case coe v1 of
             C_pair_406 v18 v19
               -> case coe v2 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C__'42'__34 v20 v21
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'pair_342 v9 v10
                           (coe
                              du_instantiate_1148 (coe v0) (coe v18) (coe v20) (coe v3) (coe v4)
                              (coe v5) (coe v16))
                           (coe
                              du_instantiate_1148 (coe v0) (coe v19) (coe v21) (coe v3) (coe v4)
                              (coe v5) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'fst_848 v12 v14
        -> case coe v1 of
             C_fst_408 v15
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fst_358
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                       (coe v0) (coe v12) (coe v4))
                    (coe
                       du_instantiate_1148 (coe v0) (coe v15)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.PolyTy.C__'42'__34 (coe v2) (coe v12))
                       (coe v3) (coe v4) (coe v5) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'snd_864 v11 v14
        -> case coe v1 of
             C_snd_410 v15
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'snd_374
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                       (coe v0) (coe v11) (coe v4))
                    (coe
                       du_instantiate_1148 (coe v0) (coe v15)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.PolyTy.C__'42'__34 (coe v11) (coe v2))
                       (coe v3) (coe v4) (coe v5) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'inl_880 v14
        -> case coe v1 of
             C_inl_412 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C__'43'__36 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inl_390
                           (coe
                              du_instantiate_1148 (coe v0) (coe v15) (coe v16) (coe v3) (coe v4)
                              (coe v5) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'inr_896 v14
        -> case coe v1 of
             C_inr_414 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C__'43'__36 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inr_406
                           (coe
                              du_instantiate_1148 (coe v0) (coe v15) (coe v17) (coe v3) (coe v4)
                              (coe v5) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'case_924 v9 v10 v11 v12 v14 v15 v20 v21 v22
        -> case coe v1 of
             C_case_416 v23 v24 v25
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'case_434 v9 v10 v11 v12
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                       (coe v0) (coe v14) (coe v4))
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                       (coe v0) (coe v15) (coe v4))
                    (coe
                       du_instantiate_1148 (coe v0) (coe v23)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.PolyTy.C__'43'__36 (coe v14) (coe v15))
                       (coe v3) (coe v4) (coe v5) (coe v20))
                    (coe
                       du_instantiate_1148 (coe v0) (coe v24) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v21))
                    (coe
                       du_instantiate_1148 (coe v0) (coe v25) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v22))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'absurd_938 v13
        -> case coe v1 of
             C_absurd_418 v14
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'absurd_448
                    (coe
                       du_instantiate_1148 (coe v0) (coe v14)
                       (coe MAlonzo.Code.Once.Spec.Core.PolyTy.C_Void_28) (coe v3)
                       (coe v4) (coe v5) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'roll_952 v13 v14
        -> case coe v1 of
             C_roll_420 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C_μ'45'type_40 v16
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'roll_462
                           (coe
                              MAlonzo.Code.Once.Spec.Core.PolyTy.du_wf'45''10218''10219'_826
                              (coe v16) (coe v5) (coe v13))
                           (coe
                              du_instantiate_1148 (coe v0) (coe v15)
                              (coe
                                 MAlonzo.Code.Once.Spec.Core.PolyTy.du_'10214'_'10215'F_58 (coe v16)
                                 (coe v2))
                              (coe v3) (coe v4) (coe v5) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'fold_972 v9 v10 v12 v16 v17 v18
        -> case coe v1 of
             C_fold_422 v19 v20
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fold_482 v9 v10
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'F_386
                       (coe v0) (coe v12) (coe v4))
                    (coe
                       MAlonzo.Code.Once.Spec.Core.PolyTy.du_wf'45''10218''10219'_826
                       (coe v12) (coe v5) (coe v16))
                    (coe
                       du_instantiate_1148 (coe v0) (coe v19)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.PolyTy.C__'8658''91'_'93'__38
                          (coe
                             MAlonzo.Code.Once.Spec.Core.PolyTy.du_'10214'_'10215'F_58 (coe v12)
                             (coe v2))
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v3))
                          (coe v2))
                       (coe v3) (coe v4) (coe v5) (coe v17))
                    (coe
                       du_instantiate_1148 (coe v0) (coe v20)
                       (coe MAlonzo.Code.Once.Spec.Core.PolyTy.C_μ'45'type_40 (coe v12))
                       (coe v3) (coe v4) (coe v5) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'unfold_994 v9 v10 v14 v17 v18 v19
        -> case coe v1 of
             C_unfold_424 v20 v21
               -> case coe v2 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C_ν'45'type_42 v22 v23
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unfold_504 v9 v10
                           (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                              (coe v0) (coe v14) (coe v4))
                           (coe
                              MAlonzo.Code.Once.Spec.Core.PolyTy.du_wf'45''10218''10219'_826
                              (coe v22) (coe v5) (coe v17))
                           (coe
                              du_instantiate_1148 (coe v0) (coe v20)
                              (coe
                                 MAlonzo.Code.Once.Spec.Core.PolyTy.C__'8658''91'_'93'__38 (coe v14)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v23))
                                 (coe
                                    MAlonzo.Code.Once.Spec.Core.PolyTy.du_'10214'_'10215'F_58
                                    (coe v22) (coe v14)))
                              (coe v3) (coe v4) (coe v5) (coe v18))
                           (coe
                              du_instantiate_1148 (coe v0) (coe v21) (coe v14) (coe v3) (coe v4)
                              (coe v5) (coe v19))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'out_1008 v11 v13 v14
        -> case coe v1 of
             C_out_426 v15
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'out_518
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'F_386
                       (coe v0) (coe v11) (coe v4))
                    (coe
                       MAlonzo.Code.Once.Spec.Core.PolyTy.du_wf'45''10218''10219'_826
                       (coe v11) (coe v5) (coe v13))
                    (coe
                       du_instantiate_1148 (coe v0) (coe v15)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.PolyTy.C_ν'45'type_42 (coe v11)
                          (coe v3))
                       (coe v3) (coe v4) (coe v5) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'coerce_1024 v14 v15
        -> case coe v1 of
             C_coerce_428 v16 v17 v18
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'coerce_534
                    (coe
                       du_'60''58''8346''45''10218''10219'_682 (coe v16) (coe v2) (coe v4)
                       (coe v14))
                    (coe
                       du_instantiate_1148 (coe v0) (coe v18) (coe v16) (coe v3) (coe v4)
                       (coe v5) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'lit'45'int_1032
        -> coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lit'45'int_542
      C_'8866'lit'45'float_1040
        -> coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lit'45'float_550
      C_'8866'prim_1054 v13
        -> case coe v1 of
             C_prim_432 v14 v15
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'prim_564
                    (coe
                       du_instantiate_1148 (coe v0) (coe v15)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.PolyTy.d_'8968'_'8969'_336 (coe v0)
                          (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_primDom_56 (coe v14)))
                       (coe v3) (coe v4) (coe v5) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'sigop_1066 v11 v12 v13 v14
        -> coe
             MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sigop_576 v11 v12 v13
             v14
      C_'8866'sub'45'eff_1082 v10 v14 v15
        -> coe
             MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618 v10 v14
             (coe
                du_instantiate_1148 (coe v0) (coe v1) (coe v2) (coe v10) (coe v4)
                (coe v5) (coe v15))
      C_'8866'sub'45'use_1098 v9 v14 v15
        -> coe
             MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'use_602 v9 v14
             (coe
                du_instantiate_1148 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v15))
      C_'8866'ref_1110 v11
        -> case coe v1 of
             C_ref_438 v12 v13
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'ref_586
                    (\ v14 v15 ->
                       coe
                         MAlonzo.Code.Once.Spec.Core.PolyTy.du_base'45''10218''10219'_788
                         (coe v13 v14) (coe v5) (coe v11 v14 v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
