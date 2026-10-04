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
d_PCtx_342 a0 a1 a2 a3 a4 = ()
data T_PCtx_342
  = C_'8709'_346 |
    C__'44'_'94'__350 T_PCtx_342
                      MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
                      MAlonzo.Code.Once.Type.T_Quantity_4
-- Once.Spec.Core.PolyTyping._,_
d__'44'__356 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  T_PCtx_342 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 -> T_PCtx_342
d__'44'__356 ~v0 ~v1 ~v2 v3 v4 = du__'44'__356 v3 v4
du__'44'__356 ::
  T_PCtx_342 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 -> T_PCtx_342
du__'44'__356 v0 v1
  = coe
      C__'44'_'94'__350 v0 v1 (coe MAlonzo.Code.Once.Type.C_Many_10)
-- Once.Spec.Core.PolyTyping.lookupP
d_lookupP_366 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  T_PCtx_342 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
d_lookupP_366 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_lookupP_366 v5 v6
du_lookupP_366 ::
  T_PCtx_342 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
du_lookupP_366 v0 v1
  = case coe v0 of
      C__'44'_'94'__350 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v4
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe du_lookupP_366 (coe v3) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.PolyTyping.PTm
d_PTm_382 a0 a1 a2 a3 a4 = ()
data T_PTm_382
  = C_var_388 MAlonzo.Code.Data.Fin.Base.T_Fin_10 |
    C_lam_390 T_PTm_382 | C_app_392 T_PTm_382 T_PTm_382 |
    C_let'8242'_394 T_PTm_382 T_PTm_382 | C_unit_396 |
    C_pair_398 T_PTm_382 T_PTm_382 | C_fst_400 T_PTm_382 |
    C_snd_402 T_PTm_382 | C_inl_404 T_PTm_382 | C_inr_406 T_PTm_382 |
    C_case_408 T_PTm_382 T_PTm_382 T_PTm_382 | C_absurd_410 T_PTm_382 |
    C_roll_412 T_PTm_382 | C_fold_414 T_PTm_382 T_PTm_382 |
    C_unfold_416 T_PTm_382 T_PTm_382 | C_out_418 T_PTm_382 |
    C_coerce_420 MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
                 MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 T_PTm_382 |
    C_lit_422 MAlonzo.Code.Once.Spec.Core.Syntax.T_Lit_14 |
    C_prim_424 MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 T_PTm_382 |
    C_sigop_426 MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
                MAlonzo.Code.Once.Type.T_Type_108 |
    C_ref_430 MAlonzo.Code.Data.Fin.Base.T_Fin_10
              (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
               MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16)
-- Once.Spec.Core.PolyTyping._⟪_⟫ᶜ
d__'10218'_'10219''7580'_436 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  T_PCtx_342 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6
d__'10218'_'10219''7580'_436 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du__'10218'_'10219''7580'_436 v3 v5 v6
du__'10218'_'10219''7580'_436 ::
  Integer ->
  T_PCtx_342 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6
du__'10218'_'10219''7580'_436 v0 v1 v2
  = case coe v1 of
      C_'8709'_346 -> coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8
      C__'44'_'94'__350 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12
             (coe du__'10218'_'10219''7580'_436 (coe v0) (coe v4) (coe v2))
             (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                (coe v0) (coe v5) (coe v2))
             v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.PolyTyping.lookup-⟪⟫
d_lookup'45''10218''10219'_458 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  T_PCtx_342 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45''10218''10219'_458 = erased
-- Once.Spec.Core.PolyTyping._⟪_⟫ₜ
d__'10218'_'10219''8348'_482 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  T_PTm_382 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d__'10218'_'10219''8348'_482 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du__'10218'_'10219''8348'_482 v3 v5 v6
du__'10218'_'10219''8348'_482 ::
  Integer ->
  T_PTm_382 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du__'10218'_'10219''8348'_482 v0 v1 v2
  = case coe v1 of
      C_var_388 v3
        -> coe MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66 (coe v3)
      C_lam_390 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
             (coe du__'10218'_'10219''8348'_482 (coe v0) (coe v3) (coe v2))
      C_app_392 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_app_70
             (coe du__'10218'_'10219''8348'_482 (coe v0) (coe v3) (coe v2))
             (coe du__'10218'_'10219''8348'_482 (coe v0) (coe v4) (coe v2))
      C_let'8242'_394 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_72
             (coe du__'10218'_'10219''8348'_482 (coe v0) (coe v3) (coe v2))
             (coe du__'10218'_'10219''8348'_482 (coe v0) (coe v4) (coe v2))
      C_unit_396 -> coe MAlonzo.Code.Once.Spec.Core.Syntax.C_unit_74
      C_pair_398 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_pair_76
             (coe du__'10218'_'10219''8348'_482 (coe v0) (coe v3) (coe v2))
             (coe du__'10218'_'10219''8348'_482 (coe v0) (coe v4) (coe v2))
      C_fst_400 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_fst_78
             (coe du__'10218'_'10219''8348'_482 (coe v0) (coe v3) (coe v2))
      C_snd_402 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_snd_80
             (coe du__'10218'_'10219''8348'_482 (coe v0) (coe v3) (coe v2))
      C_inl_404 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_inl_82
             (coe du__'10218'_'10219''8348'_482 (coe v0) (coe v3) (coe v2))
      C_inr_406 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_inr_84
             (coe du__'10218'_'10219''8348'_482 (coe v0) (coe v3) (coe v2))
      C_case_408 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_case_86
             (coe du__'10218'_'10219''8348'_482 (coe v0) (coe v3) (coe v2))
             (coe du__'10218'_'10219''8348'_482 (coe v0) (coe v4) (coe v2))
             (coe du__'10218'_'10219''8348'_482 (coe v0) (coe v5) (coe v2))
      C_absurd_410 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_absurd_88
             (coe du__'10218'_'10219''8348'_482 (coe v0) (coe v3) (coe v2))
      C_roll_412 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_roll_90
             (coe du__'10218'_'10219''8348'_482 (coe v0) (coe v3) (coe v2))
      C_fold_414 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_fold_92
             (coe du__'10218'_'10219''8348'_482 (coe v0) (coe v3) (coe v2))
             (coe du__'10218'_'10219''8348'_482 (coe v0) (coe v4) (coe v2))
      C_unfold_416 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_unfold_94
             (coe du__'10218'_'10219''8348'_482 (coe v0) (coe v3) (coe v2))
             (coe du__'10218'_'10219''8348'_482 (coe v0) (coe v4) (coe v2))
      C_out_418 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_out_96
             (coe du__'10218'_'10219''8348'_482 (coe v0) (coe v3) (coe v2))
      C_coerce_420 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_coerce_98
             (coe
                MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382 (coe v0)
                (coe v3) (coe v2))
             (coe
                MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382 (coe v0)
                (coe v4) (coe v2))
             (coe du__'10218'_'10219''8348'_482 (coe v0) (coe v5) (coe v2))
      C_lit_422 v3
        -> coe MAlonzo.Code.Once.Spec.Core.Syntax.C_lit_100 (coe v3)
      C_prim_424 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_prim_102 (coe v3)
             (coe du__'10218'_'10219''8348'_482 (coe v0) (coe v4) (coe v2))
      C_sigop_426 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_sigop_104 (coe v3) (coe v4)
      C_ref_430 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_ref_108 (coe v3)
             (coe
                (\ v5 ->
                   MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                     (coe v0) (coe v4 v5) (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.PolyTyping._<:ₚ_
d__'60''58''8346'__594 a0 a1 a2 a3 a4 a5 = ()
data T__'60''58''8346'__594
  = C_sub'45'var_600 | C_sub'45'void_604 | C_sub'45'unit_606 |
    C_sub'45'int_608 | C_sub'45'float_610 | C_sub'45'rigid_616 |
    C_sub'45'arr_632 T__'60''58''8346'__594 T__'60''58''8346'__594
                     MAlonzo.Code.Once.Type.Sub.T__'8849'π__6 |
    C_sub'45'prod_642 T__'60''58''8346'__594 T__'60''58''8346'__594 |
    C_sub'45'sum_652 T__'60''58''8346'__594 T__'60''58''8346'__594 |
    C_sub'45'μ_656 |
    C_sub'45'ν_664 MAlonzo.Code.Once.Type.Sub.T__'8849'π__6
-- Once.Spec.Core.PolyTyping.<:ₚ-⟪⟫
d_'60''58''8346''45''10218''10219'_674 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  T__'60''58''8346'__594 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
d_'60''58''8346''45''10218''10219'_674 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_'60''58''8346''45''10218''10219'_674 v4 v5 v6 v7
du_'60''58''8346''45''10218''10219'_674 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  T__'60''58''8346'__594 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
du_'60''58''8346''45''10218''10219'_674 v0 v1 v2 v3
  = let v4
          = case coe v3 of
              C_sub'45'void_604
                -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'void_52
              C_sub'45'unit_606
                -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_54
              C_sub'45'int_608 -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'int_56
              C_sub'45'float_610
                -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'float_58
              _ -> MAlonzo.RTE.mazUnreachableError in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Core.PolyTy.C_var_24 v5
           -> case coe v3 of
                C_sub'45'var_600
                  -> case coe v1 of
                       MAlonzo.Code.Once.Spec.Core.PolyTy.C_var_24 v7
                         -> coe
                              MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170 (coe v2 v5)
                       _ -> coe v4
                C_sub'45'void_604
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'void_52
                C_sub'45'unit_606
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_54
                C_sub'45'int_608 -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'int_56
                C_sub'45'float_610
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'float_58
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Core.PolyTy.C__'42'__34 v5 v6
           -> case coe v3 of
                C_sub'45'void_604
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'void_52
                C_sub'45'unit_606
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_54
                C_sub'45'int_608 -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'int_56
                C_sub'45'float_610
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'float_58
                C_sub'45'prod_642 v11 v12
                  -> case coe v1 of
                       MAlonzo.Code.Once.Spec.Core.PolyTy.C__'42'__34 v13 v14
                         -> coe
                              MAlonzo.Code.Once.Type.Sub.C_sub'45'prod_84
                              (coe
                                 du_'60''58''8346''45''10218''10219'_674 (coe v5) (coe v13) (coe v2)
                                 (coe v11))
                              (coe
                                 du_'60''58''8346''45''10218''10219'_674 (coe v6) (coe v14) (coe v2)
                                 (coe v12))
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Core.PolyTy.C__'43'__36 v5 v6
           -> case coe v3 of
                C_sub'45'void_604
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'void_52
                C_sub'45'unit_606
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_54
                C_sub'45'int_608 -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'int_56
                C_sub'45'float_610
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'float_58
                C_sub'45'sum_652 v11 v12
                  -> case coe v1 of
                       MAlonzo.Code.Once.Spec.Core.PolyTy.C__'43'__36 v13 v14
                         -> coe
                              MAlonzo.Code.Once.Type.Sub.C_sub'45'sum_94
                              (coe
                                 du_'60''58''8346''45''10218''10219'_674 (coe v5) (coe v13) (coe v2)
                                 (coe v11))
                              (coe
                                 du_'60''58''8346''45''10218''10219'_674 (coe v6) (coe v14) (coe v2)
                                 (coe v12))
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Core.PolyTy.C__'8658''91'_'93'__38 v5 v6 v7
           -> case coe v3 of
                C_sub'45'void_604
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'void_52
                C_sub'45'unit_606
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_54
                C_sub'45'int_608 -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'int_56
                C_sub'45'float_610
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'float_58
                C_sub'45'arr_632 v15 v16 v17
                  -> case coe v1 of
                       MAlonzo.Code.Once.Spec.Core.PolyTy.C__'8658''91'_'93'__38 v18 v19 v20
                         -> coe
                              MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_74
                              (coe
                                 du_'60''58''8346''45''10218''10219'_674 (coe v18) (coe v5) (coe v2)
                                 (coe v15))
                              (coe
                                 du_'60''58''8346''45''10218''10219'_674 (coe v7) (coe v20) (coe v2)
                                 (coe v16))
                              v17
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Core.PolyTy.C_μ'45'type_40 v5
           -> case coe v3 of
                C_sub'45'void_604
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'void_52
                C_sub'45'unit_606
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_54
                C_sub'45'int_608 -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'int_56
                C_sub'45'float_610
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'float_58
                C_sub'45'μ_656
                  -> case coe v1 of
                       MAlonzo.Code.Once.Spec.Core.PolyTy.C_μ'45'type_40 v7
                         -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'μ_98
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Core.PolyTy.C_ν'45'type_42 v5 v6
           -> case coe v3 of
                C_sub'45'void_604
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'void_52
                C_sub'45'unit_606
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_54
                C_sub'45'int_608 -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'int_56
                C_sub'45'float_610
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'float_58
                C_sub'45'ν_664 v10
                  -> case coe v1 of
                       MAlonzo.Code.Once.Spec.Core.PolyTy.C_ν'45'type_42 v11 v12
                         -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'ν_106 v10
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Core.PolyTy.C_rigid_44 v5 v6
           -> case coe v3 of
                C_sub'45'void_604
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'void_52
                C_sub'45'unit_606
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_54
                C_sub'45'int_608 -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'int_56
                C_sub'45'float_610
                  -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'float_58
                C_sub'45'rigid_616
                  -> case coe v1 of
                       MAlonzo.Code.Once.Spec.Core.PolyTy.C_rigid_44 v9 v10
                         -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'rigid_112
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v4)
-- Once.Spec.Core.PolyTyping._⊩_⊢[_]_∷_!_
d__'8873'_'8866''91'_'93'_'8759'_'33'__722 a0 a1 a2 a3 a4 a5 a6 a7
                                           a8 a9 a10
  = ()
data T__'8873'_'8866''91'_'93'_'8759'_'33'__722
  = C_'8866'var_734 |
    C_'8866'lam_754 MAlonzo.Code.Once.Type.T_Quantity_4
                    T__'8873'_'8866''91'_'93'_'8759'_'33'__722 |
    C_'8866'app_776 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Type.T_Quantity_4
                    MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
                    T__'8873'_'8866''91'_'93'_'8759'_'33'__722
                    T__'8873'_'8866''91'_'93'_'8759'_'33'__722 |
    C_'8866'let_798 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Surface.Context.T_Usage_60
                    MAlonzo.Code.Once.Type.T_Quantity_4
                    MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
                    T__'8873'_'8866''91'_'93'_'8759'_'33'__722
                    T__'8873'_'8866''91'_'93'_'8759'_'33'__722 |
    C_'8866'unit_804 |
    C_'8866'pair_824 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__722
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__722 |
    C_'8866'fst_840 MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
                    T__'8873'_'8866''91'_'93'_'8759'_'33'__722 |
    C_'8866'snd_856 MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
                    T__'8873'_'8866''91'_'93'_'8759'_'33'__722 |
    C_'8866'inl_872 T__'8873'_'8866''91'_'93'_'8759'_'33'__722 |
    C_'8866'inr_888 T__'8873'_'8866''91'_'93'_'8759'_'33'__722 |
    C_'8866'case_918 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                     MAlonzo.Code.Once.Type.T_Quantity_4
                     MAlonzo.Code.Once.Type.T_Quantity_4
                     MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
                     MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__722
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__722
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__722 |
    C_'8866'absurd_932 T__'8873'_'8866''91'_'93'_'8759'_'33'__722 |
    C_'8866'roll_946 MAlonzo.Code.Once.Spec.Core.PolyTy.T_WFFun_746
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__722 |
    C_'8866'fold_966 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                     MAlonzo.Code.Once.Surface.Context.T_Usage_60
                     MAlonzo.Code.Once.Spec.Core.PolyTy.T_Fun_20
                     MAlonzo.Code.Once.Spec.Core.PolyTy.T_WFFun_746
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__722
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__722 |
    C_'8866'unfold_988 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                       MAlonzo.Code.Once.Surface.Context.T_Usage_60
                       MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
                       MAlonzo.Code.Once.Spec.Core.PolyTy.T_WFFun_746
                       T__'8873'_'8866''91'_'93'_'8759'_'33'__722
                       T__'8873'_'8866''91'_'93'_'8759'_'33'__722 |
    C_'8866'out_1002 MAlonzo.Code.Once.Spec.Core.PolyTy.T_Fun_20
                     MAlonzo.Code.Once.Spec.Core.PolyTy.T_WFFun_746
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__722 |
    C_'8866'coerce_1018 T__'60''58''8346'__594
                        T__'8873'_'8866''91'_'93'_'8759'_'33'__722 |
    C_'8866'lit'45'int_1026 | C_'8866'lit'45'float_1034 |
    C_'8866'prim_1048 T__'8873'_'8866''91'_'93'_'8759'_'33'__722 |
    C_'8866'sigop_1060 MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222
                       AgdaAny MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748
                       MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 |
    C_'8866'sub'45'eff_1076 MAlonzo.Code.Once.Type.T_Purity_32
                            MAlonzo.Code.Once.Type.Sub.T__'8849'π__6
                            T__'8873'_'8866''91'_'93'_'8759'_'33'__722 |
    C_'8866'ref_1088 (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
                      MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                      MAlonzo.Code.Once.Spec.Core.PolyTy.T_Base_708)
-- Once.Spec.Core.PolyTyping.,-⟪⟫
d_'44''45''10218''10219'_1100 ::
  T_PCtx_342 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'44''45''10218''10219'_1100 = erased
-- Once.Spec.Core.PolyTyping.instantiate
d_instantiate_1126 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  Integer ->
  T_PCtx_342 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  T_PTm_382 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  T__'8873'_'8866''91'_'93'_'8759'_'33'__722 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_instantiate_1126 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 v12
                   v13
  = du_instantiate_1126 v3 v8 v9 v10 v11 v12 v13
du_instantiate_1126 ::
  Integer ->
  T_PTm_382 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  T__'8873'_'8866''91'_'93'_'8759'_'33'__722 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_instantiate_1126 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      C_'8866'var_734
        -> coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252
      C_'8866'lam_754 v11 v17
        -> case coe v1 of
             C_lam_390 v18
               -> case coe v2 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C__'8658''91'_'93'__38 v19 v20 v21
                      -> case coe v20 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v22 v23
                             -> coe
                                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272 v11
                                  (coe
                                     du_instantiate_1126 (coe v0) (coe v18) (coe v21) (coe v23)
                                     (coe v4) (coe v5) (coe v17))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'app_776 v9 v10 v11 v13 v17 v18
        -> case coe v1 of
             C_app_392 v19 v20
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294 v9 v10 v11
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                       (coe v0) (coe v13) (coe v4))
                    (coe
                       du_instantiate_1126 (coe v0) (coe v19)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.PolyTy.C__'8658''91'_'93'__38 (coe v13)
                          (coe MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v11) (coe v3))
                          (coe v2))
                       (coe v3) (coe v4) (coe v5) (coe v17))
                    (coe
                       du_instantiate_1126 (coe v0) (coe v20) (coe v13) (coe v3) (coe v4)
                       (coe v5) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'let_798 v9 v10 v11 v13 v17 v18
        -> case coe v1 of
             C_let'8242'_394 v19 v20
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316 v9 v10 v11
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                       (coe v0) (coe v13) (coe v4))
                    (coe
                       du_instantiate_1126 (coe v0) (coe v19) (coe v13) (coe v3) (coe v4)
                       (coe v5) (coe v17))
                    (coe
                       du_instantiate_1126 (coe v0) (coe v20) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'unit_804
        -> coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unit_322
      C_'8866'pair_824 v9 v10 v16 v17
        -> case coe v1 of
             C_pair_398 v18 v19
               -> case coe v2 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C__'42'__34 v20 v21
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'pair_342 v9 v10
                           (coe
                              du_instantiate_1126 (coe v0) (coe v18) (coe v20) (coe v3) (coe v4)
                              (coe v5) (coe v16))
                           (coe
                              du_instantiate_1126 (coe v0) (coe v19) (coe v21) (coe v3) (coe v4)
                              (coe v5) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'fst_840 v12 v14
        -> case coe v1 of
             C_fst_400 v15
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fst_358
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                       (coe v0) (coe v12) (coe v4))
                    (coe
                       du_instantiate_1126 (coe v0) (coe v15)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.PolyTy.C__'42'__34 (coe v2) (coe v12))
                       (coe v3) (coe v4) (coe v5) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'snd_856 v11 v14
        -> case coe v1 of
             C_snd_402 v15
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'snd_374
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                       (coe v0) (coe v11) (coe v4))
                    (coe
                       du_instantiate_1126 (coe v0) (coe v15)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.PolyTy.C__'42'__34 (coe v11) (coe v2))
                       (coe v3) (coe v4) (coe v5) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'inl_872 v14
        -> case coe v1 of
             C_inl_404 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C__'43'__36 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inl_390
                           (coe
                              du_instantiate_1126 (coe v0) (coe v15) (coe v16) (coe v3) (coe v4)
                              (coe v5) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'inr_888 v14
        -> case coe v1 of
             C_inr_406 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C__'43'__36 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inr_406
                           (coe
                              du_instantiate_1126 (coe v0) (coe v15) (coe v17) (coe v3) (coe v4)
                              (coe v5) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'case_918 v9 v10 v11 v12 v13 v15 v16 v21 v22 v23
        -> case coe v1 of
             C_case_408 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'case_436 v9 v10 v11 v12
                    v13
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                       (coe v0) (coe v15) (coe v4))
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                       (coe v0) (coe v16) (coe v4))
                    (coe
                       du_instantiate_1126 (coe v0) (coe v24)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.PolyTy.C__'43'__36 (coe v15) (coe v16))
                       (coe v3) (coe v4) (coe v5) (coe v21))
                    (coe
                       du_instantiate_1126 (coe v0) (coe v25) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v22))
                    (coe
                       du_instantiate_1126 (coe v0) (coe v26) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v23))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'absurd_932 v13
        -> case coe v1 of
             C_absurd_410 v14
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'absurd_450
                    (coe
                       du_instantiate_1126 (coe v0) (coe v14)
                       (coe MAlonzo.Code.Once.Spec.Core.PolyTy.C_Void_28) (coe v3)
                       (coe v4) (coe v5) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'roll_946 v13 v14
        -> case coe v1 of
             C_roll_412 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C_μ'45'type_40 v16
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'roll_464
                           (coe
                              MAlonzo.Code.Once.Spec.Core.PolyTy.du_wf'45''10218''10219'_826
                              (coe v16) (coe v5) (coe v13))
                           (coe
                              du_instantiate_1126 (coe v0) (coe v15)
                              (coe
                                 MAlonzo.Code.Once.Spec.Core.PolyTy.du_'10214'_'10215'F_58 (coe v16)
                                 (coe v2))
                              (coe v3) (coe v4) (coe v5) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'fold_966 v9 v10 v12 v16 v17 v18
        -> case coe v1 of
             C_fold_414 v19 v20
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fold_484 v9 v10
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'F_386
                       (coe v0) (coe v12) (coe v4))
                    (coe
                       MAlonzo.Code.Once.Spec.Core.PolyTy.du_wf'45''10218''10219'_826
                       (coe v12) (coe v5) (coe v16))
                    (coe
                       du_instantiate_1126 (coe v0) (coe v19)
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
                       du_instantiate_1126 (coe v0) (coe v20)
                       (coe MAlonzo.Code.Once.Spec.Core.PolyTy.C_μ'45'type_40 (coe v12))
                       (coe v3) (coe v4) (coe v5) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'unfold_988 v9 v10 v14 v17 v18 v19
        -> case coe v1 of
             C_unfold_416 v20 v21
               -> case coe v2 of
                    MAlonzo.Code.Once.Spec.Core.PolyTy.C_ν'45'type_42 v22 v23
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unfold_506 v9 v10
                           (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                              (coe v0) (coe v14) (coe v4))
                           (coe
                              MAlonzo.Code.Once.Spec.Core.PolyTy.du_wf'45''10218''10219'_826
                              (coe v22) (coe v5) (coe v17))
                           (coe
                              du_instantiate_1126 (coe v0) (coe v20)
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
                              du_instantiate_1126 (coe v0) (coe v21) (coe v14) (coe v3) (coe v4)
                              (coe v5) (coe v19))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'out_1002 v11 v13 v14
        -> case coe v1 of
             C_out_418 v15
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'out_520
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'F_386
                       (coe v0) (coe v11) (coe v4))
                    (coe
                       MAlonzo.Code.Once.Spec.Core.PolyTy.du_wf'45''10218''10219'_826
                       (coe v11) (coe v5) (coe v13))
                    (coe
                       du_instantiate_1126 (coe v0) (coe v15)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.PolyTy.C_ν'45'type_42 (coe v11)
                          (coe v3))
                       (coe v3) (coe v4) (coe v5) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'coerce_1018 v14 v15
        -> case coe v1 of
             C_coerce_420 v16 v17 v18
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'coerce_536
                    (coe
                       du_'60''58''8346''45''10218''10219'_674 (coe v16) (coe v2) (coe v4)
                       (coe v14))
                    (coe
                       du_instantiate_1126 (coe v0) (coe v18) (coe v16) (coe v3) (coe v4)
                       (coe v5) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'lit'45'int_1026
        -> coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lit'45'int_544
      C_'8866'lit'45'float_1034
        -> coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lit'45'float_552
      C_'8866'prim_1048 v13
        -> case coe v1 of
             C_prim_424 v14 v15
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'prim_566
                    (coe
                       du_instantiate_1126 (coe v0) (coe v15)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.PolyTy.d_'8968'_'8969'_336 (coe v0)
                          (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_primDom_56 (coe v14)))
                       (coe v3) (coe v4) (coe v5) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'sigop_1060 v11 v12 v13 v14
        -> coe
             MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sigop_578 v11 v12 v13
             v14
      C_'8866'sub'45'eff_1076 v10 v14 v15
        -> coe
             MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_604 v10 v14
             (coe
                du_instantiate_1126 (coe v0) (coe v1) (coe v2) (coe v10) (coe v4)
                (coe v5) (coe v15))
      C_'8866'ref_1088 v11
        -> case coe v1 of
             C_ref_430 v12 v13
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'ref_588
                    (\ v14 v15 ->
                       coe
                         MAlonzo.Code.Once.Spec.Core.PolyTy.du_base'45''10218''10219'_788
                         (coe v13 v14) (coe v5) (coe v11 v14 v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
