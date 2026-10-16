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

module MAlonzo.Code.Once.Lang.Core.PolyTyping where

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
import qualified MAlonzo.Code.Once.Lang.Core.PolyTy
import qualified MAlonzo.Code.Once.Lang.Core.Syntax
import qualified MAlonzo.Code.Once.Lang.Core.Typing
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Name

-- Once.Lang.Core.PolyTyping.G.Lit
d_Lit_18 a0 a1 a2 = ()
-- Once.Lang.Core.PolyTyping.G.Prim
d_Prim_20 a0 a1 a2 = ()
-- Once.Lang.Core.PolyTyping.G.Tm
d_Tm_26 a0 a1 a2 a3 = ()
-- Once.Lang.Core.PolyTyping.G.primCod
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
-- Once.Lang.Core.PolyTyping.G.primDom
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
-- Once.Lang.Core.PolyTyping.GT._⊢[_]_∷_!_
d__'8866''91'_'93'_'8759'_'33'__248 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.Lang.Core.PolyTyping.PCtx
d_PCtx_366 a0 a1 a2 a3 a4 = ()
data T_PCtx_366
  = C_'8709'_370 |
    C__'44'_'94'__374 T_PCtx_366
                      MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16
                      MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
-- Once.Lang.Core.PolyTyping._,_
d__'44'__380 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  T_PCtx_366 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16 -> T_PCtx_366
d__'44'__380 ~v0 ~v1 ~v2 v3 v4 = du__'44'__380 v3 v4
du__'44'__380 ::
  T_PCtx_366 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16 -> T_PCtx_366
du__'44'__380 v0 v1
  = coe
      C__'44'_'94'__374 v0 v1
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
-- Once.Lang.Core.PolyTyping.lookupP
d_lookupP_390 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  T_PCtx_366 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16
d_lookupP_390 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_lookupP_390 v5 v6
du_lookupP_390 ::
  T_PCtx_366 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16
du_lookupP_390 v0 v1
  = case coe v0 of
      C__'44'_'94'__374 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v4
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe du_lookupP_390 (coe v3) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.PolyTyping.PTm
d_PTm_406 a0 a1 a2 a3 a4 = ()
data T_PTm_406
  = C_var_412 MAlonzo.Code.Data.Fin.Base.T_Fin_10 |
    C_lam_414 MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16
              MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
              MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 T_PTm_406 |
    C_app_416 T_PTm_406 T_PTm_406 |
    C_let'8242'_418 MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
                    T_PTm_406 T_PTm_406 |
    C_unit_420 | C_pair_422 T_PTm_406 T_PTm_406 | C_fst_424 T_PTm_406 |
    C_snd_426 T_PTm_406 |
    C_inl_428 MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16 T_PTm_406 |
    C_inr_430 MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16 T_PTm_406 |
    C_case_432 MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
               MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 T_PTm_406 T_PTm_406
               T_PTm_406 |
    C_absurd_434 MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16 T_PTm_406 |
    C_roll_436 MAlonzo.Code.Once.Lang.Core.PolyTy.T_Fun_20 T_PTm_406 |
    C_fold_438 MAlonzo.Code.Once.Lang.Core.PolyTy.T_Fun_20 T_PTm_406
               T_PTm_406 |
    C_unfold_440 MAlonzo.Code.Once.Lang.Core.PolyTy.T_Fun_20 T_PTm_406
                 T_PTm_406 |
    C_iter_442 T_PTm_406 T_PTm_406 | C_out_444 T_PTm_406 |
    C_coerce_446 MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16
                 MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16 T_PTm_406 |
    C_lit_448 MAlonzo.Code.Once.Lang.Core.Syntax.T_Lit_14 |
    C_prim_450 MAlonzo.Code.Once.Lang.Core.Syntax.T_Prim_20 T_PTm_406 |
    C_sigop_452 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
                MAlonzo.Code.Once.Lang.Type.T_Type_8 |
    C_ref_456 MAlonzo.Code.Data.Fin.Base.T_Fin_10
              (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
               MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16)
-- Once.Lang.Core.PolyTyping._⟪_⟫ᶜ
d__'10218'_'10219''7580'_462 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  T_PCtx_366 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6
d__'10218'_'10219''7580'_462 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du__'10218'_'10219''7580'_462 v3 v5 v6
du__'10218'_'10219''7580'_462 ::
  Integer ->
  T_PCtx_366 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6
du__'10218'_'10219''7580'_462 v0 v1 v2
  = case coe v1 of
      C_'8709'_370 -> coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8
      C__'44'_'94'__374 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12
             (coe du__'10218'_'10219''7580'_462 (coe v0) (coe v4) (coe v2))
             (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                (coe v0) (coe v5) (coe v2))
             v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.PolyTyping.lookup-⟪⟫
d_lookup'45''10218''10219'_484 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  T_PCtx_366 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45''10218''10219'_484 = erased
-- Once.Lang.Core.PolyTyping._⟪_⟫ₜ
d__'10218'_'10219''8348'_508 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  T_PTm_406 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d__'10218'_'10219''8348'_508 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du__'10218'_'10219''8348'_508 v3 v5 v6
du__'10218'_'10219''8348'_508 ::
  Integer ->
  T_PTm_406 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du__'10218'_'10219''8348'_508 v0 v1 v2
  = case coe v1 of
      C_var_412 v3
        -> coe MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66 (coe v3)
      C_lam_414 v3 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344 (coe v0)
                (coe v3) (coe v2))
             (coe v4) (coe v5)
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v6) (coe v2))
      C_app_416 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.Syntax.C_app_70
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v3) (coe v2))
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v4) (coe v2))
      C_let'8242'_418 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.Syntax.C_let'8242'_72 (coe v3)
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v4) (coe v2))
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v5) (coe v2))
      C_unit_420 -> coe MAlonzo.Code.Once.Lang.Core.Syntax.C_unit_74
      C_pair_422 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.Syntax.C_pair_76
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v3) (coe v2))
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v4) (coe v2))
      C_fst_424 v3
        -> coe
             MAlonzo.Code.Once.Lang.Core.Syntax.C_fst_78
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v3) (coe v2))
      C_snd_426 v3
        -> coe
             MAlonzo.Code.Once.Lang.Core.Syntax.C_snd_80
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v3) (coe v2))
      C_inl_428 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.Syntax.C_inl_82
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344 (coe v0)
                (coe v3) (coe v2))
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v4) (coe v2))
      C_inr_430 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.Syntax.C_inr_84
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344 (coe v0)
                (coe v3) (coe v2))
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v4) (coe v2))
      C_case_432 v3 v4 v5 v6 v7
        -> coe
             MAlonzo.Code.Once.Lang.Core.Syntax.C_case_86 (coe v3) (coe v4)
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v5) (coe v2))
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v6) (coe v2))
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v7) (coe v2))
      C_absurd_434 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.Syntax.C_absurd_88
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344 (coe v0)
                (coe v3) (coe v2))
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v4) (coe v2))
      C_roll_436 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.Syntax.C_roll_90
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'F_348 (coe v0)
                (coe v3) (coe v2))
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v4) (coe v2))
      C_fold_438 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.Syntax.C_fold_92
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'F_348 (coe v0)
                (coe v3) (coe v2))
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v4) (coe v2))
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v5) (coe v2))
      C_unfold_440 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.Syntax.C_unfold_94
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'F_348 (coe v0)
                (coe v3) (coe v2))
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v4) (coe v2))
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v5) (coe v2))
      C_iter_442 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.Syntax.C_iter_96
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v3) (coe v2))
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v4) (coe v2))
      C_out_444 v3
        -> coe
             MAlonzo.Code.Once.Lang.Core.Syntax.C_out_98
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v3) (coe v2))
      C_coerce_446 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Core.Syntax.C_coerce_100
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344 (coe v0)
                (coe v3) (coe v2))
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344 (coe v0)
                (coe v4) (coe v2))
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v5) (coe v2))
      C_lit_448 v3
        -> coe MAlonzo.Code.Once.Lang.Core.Syntax.C_lit_102 (coe v3)
      C_prim_450 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.Syntax.C_prim_104 (coe v3)
             (coe du__'10218'_'10219''8348'_508 (coe v0) (coe v4) (coe v2))
      C_sigop_452 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.Syntax.C_sigop_106 (coe v3) (coe v4)
      C_ref_456 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Core.Syntax.C_ref_110 (coe v3)
             (coe
                (\ v5 ->
                   MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                     (coe v0) (coe v4 v5) (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.PolyTyping._<:ₚ_
d__'60''58''8346'__650 a0 a1 a2 a3 a4 a5 = ()
data T__'60''58''8346'__650
  = C_sub'45'var_656 | C_sub'45'void_660 | C_sub'45'unit_662 |
    C_sub'45'int_664 | C_sub'45'float_666 | C_sub'45'rigid_672 |
    C_sub'45'arr_688 T__'60''58''8346'__650 T__'60''58''8346'__650
                     MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 |
    C_sub'45'prod_698 T__'60''58''8346'__650 T__'60''58''8346'__650 |
    C_sub'45'sum_708 T__'60''58''8346'__650 T__'60''58''8346'__650 |
    C_sub'45'μ_712 |
    C_sub'45'ν_720 MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
-- Once.Lang.Core.PolyTyping.<:ₚ-⟪⟫
d_'60''58''8346''45''10218''10219'_730 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  T__'60''58''8346'__650 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
d_'60''58''8346''45''10218''10219'_730 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_'60''58''8346''45''10218''10219'_730 v4 v5 v6 v7
du_'60''58''8346''45''10218''10219'_730 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  T__'60''58''8346'__650 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
du_'60''58''8346''45''10218''10219'_730 v0 v1 v2 v3
  = let v4
          = case coe v3 of
              C_sub'45'void_660
                -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'void_34
              C_sub'45'unit_662
                -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'unit_36
              C_sub'45'int_664
                -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'int_38
              C_sub'45'float_666
                -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'float_40
              _ -> MAlonzo.RTE.mazUnreachableError in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Lang.Core.PolyTy.C_var_24 v5
           -> case coe v3 of
                C_sub'45'var_656
                  -> case coe v1 of
                       MAlonzo.Code.Once.Lang.Core.PolyTy.C_var_24 v7
                         -> coe
                              MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_102 (coe v2 v5)
                       _ -> coe v4
                C_sub'45'void_660
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'void_34
                C_sub'45'unit_662
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'unit_36
                C_sub'45'int_664
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'int_38
                C_sub'45'float_666
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'float_40
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Lang.Core.PolyTy.C__'42'__34 v5 v6
           -> case coe v3 of
                C_sub'45'void_660
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'void_34
                C_sub'45'unit_662
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'unit_36
                C_sub'45'int_664
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'int_38
                C_sub'45'float_666
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'float_40
                C_sub'45'prod_698 v11 v12
                  -> case coe v1 of
                       MAlonzo.Code.Once.Lang.Core.PolyTy.C__'42'__34 v13 v14
                         -> coe
                              MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'prod_66
                              (coe
                                 du_'60''58''8346''45''10218''10219'_730 (coe v5) (coe v13) (coe v2)
                                 (coe v11))
                              (coe
                                 du_'60''58''8346''45''10218''10219'_730 (coe v6) (coe v14) (coe v2)
                                 (coe v12))
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Lang.Core.PolyTy.C__'43'__36 v5 v6
           -> case coe v3 of
                C_sub'45'void_660
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'void_34
                C_sub'45'unit_662
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'unit_36
                C_sub'45'int_664
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'int_38
                C_sub'45'float_666
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'float_40
                C_sub'45'sum_708 v11 v12
                  -> case coe v1 of
                       MAlonzo.Code.Once.Lang.Core.PolyTy.C__'43'__36 v13 v14
                         -> coe
                              MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'sum_76
                              (coe
                                 du_'60''58''8346''45''10218''10219'_730 (coe v5) (coe v13) (coe v2)
                                 (coe v11))
                              (coe
                                 du_'60''58''8346''45''10218''10219'_730 (coe v6) (coe v14) (coe v2)
                                 (coe v12))
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Lang.Core.PolyTy.C__'8658''91'_'93'__38 v5 v6 v7
           -> case coe v3 of
                C_sub'45'void_660
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'void_34
                C_sub'45'unit_662
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'unit_36
                C_sub'45'int_664
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'int_38
                C_sub'45'float_666
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'float_40
                C_sub'45'arr_688 v15 v16 v17
                  -> case coe v1 of
                       MAlonzo.Code.Once.Lang.Core.PolyTy.C__'8658''91'_'93'__38 v18 v19 v20
                         -> coe
                              MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_56
                              (coe
                                 du_'60''58''8346''45''10218''10219'_730 (coe v18) (coe v5) (coe v2)
                                 (coe v15))
                              (coe
                                 du_'60''58''8346''45''10218''10219'_730 (coe v7) (coe v20) (coe v2)
                                 (coe v16))
                              v17
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Lang.Core.PolyTy.C_μ'45'type_40 v5
           -> case coe v3 of
                C_sub'45'void_660
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'void_34
                C_sub'45'unit_662
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'unit_36
                C_sub'45'int_664
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'int_38
                C_sub'45'float_666
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'float_40
                C_sub'45'μ_712
                  -> case coe v1 of
                       MAlonzo.Code.Once.Lang.Core.PolyTy.C_μ'45'type_40 v7
                         -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'μ_80
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Lang.Core.PolyTy.C_ν'45'type_42 v5 v6
           -> case coe v3 of
                C_sub'45'void_660
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'void_34
                C_sub'45'unit_662
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'unit_36
                C_sub'45'int_664
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'int_38
                C_sub'45'float_666
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'float_40
                C_sub'45'ν_720 v10
                  -> case coe v1 of
                       MAlonzo.Code.Once.Lang.Core.PolyTy.C_ν'45'type_42 v11 v12
                         -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'ν_88 v10
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Lang.Core.PolyTy.C_rigid_44 v5 v6
           -> case coe v3 of
                C_sub'45'void_660
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'void_34
                C_sub'45'unit_662
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'unit_36
                C_sub'45'int_664
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'int_38
                C_sub'45'float_666
                  -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'float_40
                C_sub'45'rigid_672
                  -> case coe v1 of
                       MAlonzo.Code.Once.Lang.Core.PolyTy.C_rigid_44 v9 v10
                         -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'rigid_94
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v4)
-- Once.Lang.Core.PolyTyping._⊩_⊢[_]_∷_!_
d__'8873'_'8866''91'_'93'_'8759'_'33'__778 a0 a1 a2 a3 a4 a5 a6 a7
                                           a8 a9 a10
  = ()
data T__'8873'_'8866''91'_'93'_'8759'_'33'__778
  = C_'8866'var_790 |
    C_'8866'lam_810 MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
                    T__'8873'_'8866''91'_'93'_'8759'_'33'__778 |
    C_'8866'app_836 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8
                    MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                    MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                    MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                    MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16
                    T__'8873'_'8866''91'_'93'_'8759'_'33'__778
                    T__'8873'_'8866''91'_'93'_'8759'_'33'__778 |
    C_'8866'let_860 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Context.T_Usage_46
                    MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                    MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                    MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16
                    T__'8873'_'8866''91'_'93'_'8759'_'33'__778
                    T__'8873'_'8866''91'_'93'_'8759'_'33'__778 |
    C_'8866'unit_866 |
    C_'8866'pair_888 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                     MAlonzo.Code.Once.Lang.Context.T_Usage_46
                     MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                     MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__778
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__778 |
    C_'8866'fst_904 MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16
                    T__'8873'_'8866''91'_'93'_'8759'_'33'__778 |
    C_'8866'snd_920 MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16
                    T__'8873'_'8866''91'_'93'_'8759'_'33'__778 |
    C_'8866'inl_936 T__'8873'_'8866''91'_'93'_'8759'_'33'__778 |
    C_'8866'inr_952 T__'8873'_'8866''91'_'93'_'8759'_'33'__778 |
    C_'8866'case_982 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                     MAlonzo.Code.Once.Lang.Context.T_Usage_46
                     MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                     MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                     MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16
                     MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__778
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__778
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__778 |
    C_'8866'absurd_996 T__'8873'_'8866''91'_'93'_'8759'_'33'__778 |
    C_'8866'roll_1010 MAlonzo.Code.Once.Lang.Core.PolyTy.T_WFFun_708
                      T__'8873'_'8866''91'_'93'_'8759'_'33'__778 |
    C_'8866'fold_1034 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                      MAlonzo.Code.Once.Lang.Context.T_Usage_46
                      MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                      MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                      MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                      MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                      MAlonzo.Code.Once.Lang.Core.PolyTy.T_WFFun_708
                      T__'8873'_'8866''91'_'93'_'8759'_'33'__778
                      T__'8873'_'8866''91'_'93'_'8759'_'33'__778 |
    C_'8866'unfold_1058 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                        MAlonzo.Code.Once.Lang.Context.T_Usage_46
                        MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                        MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                        MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16
                        MAlonzo.Code.Once.Lang.Core.PolyTy.T_WFFun_708
                        T__'8873'_'8866''91'_'93'_'8759'_'33'__778
                        T__'8873'_'8866''91'_'93'_'8759'_'33'__778 |
    C_'8866'iter_1080 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                      MAlonzo.Code.Once.Lang.Context.T_Usage_46
                      MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                      MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                      MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16
                      T__'8873'_'8866''91'_'93'_'8759'_'33'__778
                      T__'8873'_'8866''91'_'93'_'8759'_'33'__778 |
    C_'8866'out_1096 MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                     MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                     MAlonzo.Code.Once.Lang.Core.PolyTy.T_Fun_20
                     MAlonzo.Code.Once.Lang.Core.PolyTy.T_WFFun_708
                     T__'8873'_'8866''91'_'93'_'8759'_'33'__778 |
    C_'8866'coerce_1112 T__'60''58''8346'__650
                        T__'8873'_'8866''91'_'93'_'8759'_'33'__778 |
    C_'8866'lit'45'int_1120 | C_'8866'lit'45'float_1128 |
    C_'8866'prim_1142 T__'8873'_'8866''91'_'93'_'8759'_'33'__778 |
    C_'8866'sigop_1154 MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34
                       AgdaAny MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68
                       MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 |
    C_'8866'sigop'8314'_1170 MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                             MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34
                             MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_48 AgdaAny
                             MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68
                             MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 |
    C_'8866'sub'45'eff_1186 MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32
                            MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
                            T__'8873'_'8866''91'_'93'_'8759'_'33'__778 |
    C_'8866'sub'45'use_1202 MAlonzo.Code.Once.Lang.Context.T_Usage_46
                            MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
                            T__'8873'_'8866''91'_'93'_'8759'_'33'__778 |
    C_'8866'ref_1214 (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
                      MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                      MAlonzo.Code.Once.Lang.Core.PolyTy.T_Base_670)
-- Once.Lang.Core.PolyTyping.instantiate
d_instantiate_1234 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  Integer ->
  T_PCtx_366 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  T_PTm_406 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  T__'8873'_'8866''91'_'93'_'8759'_'33'__778 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_instantiate_1234 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10 v11
                   v12 v13
  = du_instantiate_1234 v3 v8 v9 v11 v12 v13
du_instantiate_1234 ::
  Integer ->
  T_PTm_406 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  T__'8873'_'8866''91'_'93'_'8759'_'33'__778 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_instantiate_1234 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_'8866'var_790
        -> coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256
      C_'8866'lam_810 v10 v16
        -> case coe v1 of
             C_lam_414 v17 v18 v19 v20
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Core.PolyTy.C__'8658''91'_'93'__38 v21 v22 v23
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276 v10
                           (coe
                              du_instantiate_1234 (coe v0) (coe v20) (coe v23) (coe v3) (coe v4)
                              (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'app_836 v8 v9 v10 v11 v12 v13 v14 v18 v19
        -> case coe v1 of
             C_app_416 v20 v21
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'app_302 v8 v9 v10 v11
                    v12 v13
                    (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0) (coe v14) (coe v3))
                    (coe
                       du_instantiate_1234 (coe v0) (coe v20)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.PolyTy.C__'8658''91'_'93'__38 (coe v14)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 (coe v10)
                             (coe v11))
                          (coe v2))
                       (coe v3) (coe v4) (coe v18))
                    (coe
                       du_instantiate_1234 (coe v0) (coe v21) (coe v14) (coe v3) (coe v4)
                       (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'let_860 v8 v9 v11 v12 v13 v17 v18
        -> case coe v1 of
             C_let'8242'_418 v19 v20 v21
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'let_326 v8 v9 v11 v12
                    (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0) (coe v13) (coe v3))
                    (coe
                       du_instantiate_1234 (coe v0) (coe v20) (coe v13) (coe v3) (coe v4)
                       (coe v17))
                    (coe
                       du_instantiate_1234 (coe v0) (coe v21) (coe v2) (coe v3) (coe v4)
                       (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'unit_866
        -> coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'unit_332
      C_'8866'pair_888 v8 v9 v10 v11 v16 v17
        -> case coe v1 of
             C_pair_422 v18 v19
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Core.PolyTy.C__'42'__34 v20 v21
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'pair_354 v8 v9 v10 v11
                           (coe
                              du_instantiate_1234 (coe v0) (coe v18) (coe v20) (coe v3) (coe v4)
                              (coe v16))
                           (coe
                              du_instantiate_1234 (coe v0) (coe v19) (coe v21) (coe v3) (coe v4)
                              (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'fst_904 v11 v13
        -> case coe v1 of
             C_fst_424 v14
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'fst_370
                    (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0) (coe v11) (coe v3))
                    (coe
                       du_instantiate_1234 (coe v0) (coe v14)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.PolyTy.C__'42'__34 (coe v2) (coe v11))
                       (coe v3) (coe v4) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'snd_920 v10 v13
        -> case coe v1 of
             C_snd_426 v14
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'snd_386
                    (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0) (coe v10) (coe v3))
                    (coe
                       du_instantiate_1234 (coe v0) (coe v14)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.PolyTy.C__'42'__34 (coe v10) (coe v2))
                       (coe v3) (coe v4) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'inl_936 v13
        -> case coe v1 of
             C_inl_428 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Core.PolyTy.C__'43'__36 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'inl_402
                           (coe
                              du_instantiate_1234 (coe v0) (coe v15) (coe v16) (coe v3) (coe v4)
                              (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'inr_952 v13
        -> case coe v1 of
             C_inr_430 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Core.PolyTy.C__'43'__36 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'inr_418
                           (coe
                              du_instantiate_1234 (coe v0) (coe v15) (coe v17) (coe v3) (coe v4)
                              (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'case_982 v8 v9 v12 v13 v14 v15 v20 v21 v22
        -> case coe v1 of
             C_case_432 v23 v24 v25 v26 v27
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'case_448 v8 v9 v12 v13
                    (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0) (coe v14) (coe v3))
                    (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0) (coe v15) (coe v3))
                    (coe
                       du_instantiate_1234 (coe v0) (coe v25)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.PolyTy.C__'43'__36 (coe v14) (coe v15))
                       (coe v3) (coe v4) (coe v20))
                    (coe
                       du_instantiate_1234 (coe v0) (coe v26) (coe v2) (coe v3) (coe v4)
                       (coe v21))
                    (coe
                       du_instantiate_1234 (coe v0) (coe v27) (coe v2) (coe v3) (coe v4)
                       (coe v22))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'absurd_996 v12
        -> case coe v1 of
             C_absurd_434 v13 v14
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'absurd_462
                    (coe
                       du_instantiate_1234 (coe v0) (coe v14)
                       (coe MAlonzo.Code.Once.Lang.Core.PolyTy.C_Void_28) (coe v3)
                       (coe v4) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'roll_1010 v12 v13
        -> case coe v1 of
             C_roll_436 v14 v15
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'roll_476
                    (coe
                       MAlonzo.Code.Once.Lang.Core.PolyTy.du_wf'45''10218''10219'_788
                       (coe v14) (coe v4) (coe v12))
                    (coe
                       du_instantiate_1234 (coe v0) (coe v15)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.PolyTy.du_'10214'_'10215'F_58 (coe v14)
                          (coe MAlonzo.Code.Once.Lang.Core.PolyTy.C_μ'45'type_40 (coe v14)))
                       (coe v3) (coe v4) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'fold_1034 v8 v9 v10 v11 v12 v17 v18 v19 v20
        -> case coe v1 of
             C_fold_438 v21 v22 v23
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'fold_500 v8 v9 v10 v11
                    v12 v17
                    (coe
                       MAlonzo.Code.Once.Lang.Core.PolyTy.du_wf'45''10218''10219'_788
                       (coe v21) (coe v4) (coe v18))
                    (coe
                       du_instantiate_1234 (coe v0) (coe v22)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.PolyTy.C__'8658''91'_'93'__38
                          (coe
                             MAlonzo.Code.Once.Lang.Core.PolyTy.du_'10214'_'10215'F_58 (coe v21)
                             (coe v2))
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v10))
                          (coe v2))
                       (coe v3) (coe v4) (coe v19))
                    (coe
                       du_instantiate_1234 (coe v0) (coe v23)
                       (coe MAlonzo.Code.Once.Lang.Core.PolyTy.C_μ'45'type_40 (coe v21))
                       (coe v3) (coe v4) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'unfold_1058 v8 v9 v11 v12 v14 v17 v18 v19
        -> case coe v1 of
             C_unfold_440 v20 v21 v22
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Core.PolyTy.C_ν'45'type_42 v23 v24
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'unfold_524 v8 v9 v11 v12
                           (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                              (coe v0) (coe v14) (coe v3))
                           (coe
                              MAlonzo.Code.Once.Lang.Core.PolyTy.du_wf'45''10218''10219'_788
                              (coe v20) (coe v4) (coe v17))
                           (coe
                              du_instantiate_1234 (coe v0) (coe v21)
                              (coe
                                 MAlonzo.Code.Once.Lang.Core.PolyTy.C__'8658''91'_'93'__38 (coe v14)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v24))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Core.PolyTy.du_'10214'_'10215'F_58
                                    (coe v20) (coe v14)))
                              (coe v3) (coe v4) (coe v18))
                           (coe
                              du_instantiate_1234 (coe v0) (coe v22) (coe v14) (coe v3) (coe v4)
                              (coe v19))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'iter_1080 v8 v9 v10 v11 v12 v16 v17
        -> case coe v1 of
             C_iter_442 v18 v19
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'iter_562 v8 v9 v10 v11
                    (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0) (coe v12) (coe v3))
                    (coe
                       du_instantiate_1234 (coe v0) (coe v18)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.PolyTy.C__'8658''91'_'93'__38 (coe v12)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                          (coe
                             MAlonzo.Code.Once.Lang.Core.PolyTy.C__'43'__36 (coe v2)
                             (coe
                                MAlonzo.Code.Once.Lang.Core.PolyTy.C__'8658''91'_'93'__38
                                (coe MAlonzo.Code.Once.Lang.Core.PolyTy.C_Unit_26)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38))
                                (coe
                                   MAlonzo.Code.Once.Lang.Core.PolyTy.C__'43'__36 (coe v2)
                                   (coe v12)))))
                       (coe v3) (coe v4) (coe v16))
                    (coe
                       du_instantiate_1234 (coe v0) (coe v19) (coe v12) (coe v3) (coe v4)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'out_1096 v9 v10 v11 v13 v14
        -> case coe v1 of
             C_out_444 v15
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'out_540 v9 v10
                    (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'F_348
                       (coe v0) (coe v11) (coe v3))
                    (coe
                       MAlonzo.Code.Once.Lang.Core.PolyTy.du_wf'45''10218''10219'_788
                       (coe v11) (coe v4) (coe v13))
                    (coe
                       du_instantiate_1234 (coe v0) (coe v15)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.PolyTy.C_ν'45'type_42 (coe v11)
                          (coe v9))
                       (coe v3) (coe v4) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'coerce_1112 v13 v14
        -> case coe v1 of
             C_coerce_446 v15 v16 v17
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'coerce_578
                    (coe
                       du_'60''58''8346''45''10218''10219'_730 (coe v15) (coe v2) (coe v3)
                       (coe v13))
                    (coe
                       du_instantiate_1234 (coe v0) (coe v17) (coe v15) (coe v3) (coe v4)
                       (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'lit'45'int_1120
        -> coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lit'45'int_586
      C_'8866'lit'45'float_1128
        -> coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lit'45'float_594
      C_'8866'prim_1142 v12
        -> case coe v1 of
             C_prim_450 v13 v14
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'prim_608
                    (coe
                       du_instantiate_1234 (coe v0) (coe v14)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.PolyTy.d_'8968'_'8969'_298 (coe v0)
                          (coe MAlonzo.Code.Once.Lang.Core.Syntax.du_primDom_56 (coe v13)))
                       (coe v3) (coe v4) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8866'sigop_1154 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sigop_620 v10 v11 v12
             v13
      C_'8866'sigop'8314'_1170 v11 v13 v14 v15 v16 v17
        -> coe
             MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sigop'8314'_636 v11 v13
             v14 v15 v16 v17
      C_'8866'sub'45'eff_1186 v9 v13 v14
        -> coe
             MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678 v9 v13
             (coe
                du_instantiate_1234 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v14))
      C_'8866'sub'45'use_1202 v8 v13 v14
        -> coe
             MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'use_662 v8 v13
             (coe
                du_instantiate_1234 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v14))
      C_'8866'ref_1214 v10
        -> case coe v1 of
             C_ref_456 v11 v12
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'ref_646
                    (\ v13 v14 ->
                       coe
                         MAlonzo.Code.Once.Lang.Core.PolyTy.du_base'45''10218''10219'_750
                         (coe v12 v13) (coe v4) (coe v10 v13 v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
