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

module MAlonzo.Code.Once.Internal.Core.Syntax where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Internal.Core.PolyTy
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name

-- Once.Internal.Core.Syntax.Lit
d_Lit_14 a0 a1 a2 = ()
data T_Lit_14
  = C_lit'45'int_16 Integer |
    C_lit'45'float_18 MAlonzo.Code.Once.Spec.Float.Decimal.T_Decimal_8
-- Once.Internal.Core.Syntax.Prim
d_Prim_20 a0 a1 a2 = ()
data T_Prim_20
  = C_p'45'add_22 | C_p'45'sub_24 | C_p'45'mul_26 | C_p'45'div_28 |
    C_p'45'mod_30 | C_p'45'neg_32 | C_p'45'lt_34 | C_p'45'le_36 |
    C_p'45'gt_38 | C_p'45'ge_40 | C_p'45'eq_42 | C_p'45'ne_44 |
    C_p'45'fadd_46 | C_p'45'fsub_48 | C_p'45'fmul_50 | C_p'45'fdiv_52 |
    C_p'45'i2f_54
-- Once.Internal.Core.Syntax.primDom
d_primDom_56 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  T_Prim_20 -> MAlonzo.Code.Once.Internal.Type.T_Type_8
d_primDom_56 ~v0 ~v1 ~v2 v3 = du_primDom_56 v3
du_primDom_56 ::
  T_Prim_20 -> MAlonzo.Code.Once.Internal.Type.T_Type_8
du_primDom_56 v0
  = case coe v0 of
      C_p'45'add_22
        -> coe
             MAlonzo.Code.Once.Internal.Type.C__'42'__24
             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
      C_p'45'sub_24
        -> coe
             MAlonzo.Code.Once.Internal.Type.C__'42'__24
             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
      C_p'45'mul_26
        -> coe
             MAlonzo.Code.Once.Internal.Type.C__'42'__24
             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
      C_p'45'div_28
        -> coe
             MAlonzo.Code.Once.Internal.Type.C__'42'__24
             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
      C_p'45'mod_30
        -> coe
             MAlonzo.Code.Once.Internal.Type.C__'42'__24
             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
      C_p'45'neg_32 -> coe MAlonzo.Code.Once.Internal.Type.C_Int_34
      C_p'45'lt_34
        -> coe
             MAlonzo.Code.Once.Internal.Type.C__'42'__24
             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
      C_p'45'le_36
        -> coe
             MAlonzo.Code.Once.Internal.Type.C__'42'__24
             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
      C_p'45'gt_38
        -> coe
             MAlonzo.Code.Once.Internal.Type.C__'42'__24
             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
      C_p'45'ge_40
        -> coe
             MAlonzo.Code.Once.Internal.Type.C__'42'__24
             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
      C_p'45'eq_42
        -> coe
             MAlonzo.Code.Once.Internal.Type.C__'42'__24
             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
      C_p'45'ne_44
        -> coe
             MAlonzo.Code.Once.Internal.Type.C__'42'__24
             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
      C_p'45'fadd_46
        -> coe
             MAlonzo.Code.Once.Internal.Type.C__'42'__24
             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
      C_p'45'fsub_48
        -> coe
             MAlonzo.Code.Once.Internal.Type.C__'42'__24
             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
      C_p'45'fmul_50
        -> coe
             MAlonzo.Code.Once.Internal.Type.C__'42'__24
             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
      C_p'45'fdiv_52
        -> coe
             MAlonzo.Code.Once.Internal.Type.C__'42'__24
             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
      C_p'45'i2f_54 -> coe MAlonzo.Code.Once.Internal.Type.C_Int_34
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.Syntax.primCod
d_primCod_58 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  T_Prim_20 -> MAlonzo.Code.Once.Internal.Type.T_Type_8
d_primCod_58 ~v0 ~v1 ~v2 v3 = du_primCod_58 v3
du_primCod_58 ::
  T_Prim_20 -> MAlonzo.Code.Once.Internal.Type.T_Type_8
du_primCod_58 v0
  = case coe v0 of
      C_p'45'add_22 -> coe MAlonzo.Code.Once.Internal.Type.C_Int_34
      C_p'45'sub_24 -> coe MAlonzo.Code.Once.Internal.Type.C_Int_34
      C_p'45'mul_26 -> coe MAlonzo.Code.Once.Internal.Type.C_Int_34
      C_p'45'div_28 -> coe MAlonzo.Code.Once.Internal.Type.C_Int_34
      C_p'45'mod_30 -> coe MAlonzo.Code.Once.Internal.Type.C_Int_34
      C_p'45'neg_32 -> coe MAlonzo.Code.Once.Internal.Type.C_Int_34
      C_p'45'lt_34
        -> coe
             MAlonzo.Code.Once.Internal.Type.C__'43'__26
             (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
             (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
      C_p'45'le_36
        -> coe
             MAlonzo.Code.Once.Internal.Type.C__'43'__26
             (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
             (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
      C_p'45'gt_38
        -> coe
             MAlonzo.Code.Once.Internal.Type.C__'43'__26
             (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
             (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
      C_p'45'ge_40
        -> coe
             MAlonzo.Code.Once.Internal.Type.C__'43'__26
             (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
             (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
      C_p'45'eq_42
        -> coe
             MAlonzo.Code.Once.Internal.Type.C__'43'__26
             (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
             (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
      C_p'45'ne_44
        -> coe
             MAlonzo.Code.Once.Internal.Type.C__'43'__26
             (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
             (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
      C_p'45'fadd_46 -> coe MAlonzo.Code.Once.Internal.Type.C_Float_36
      C_p'45'fsub_48 -> coe MAlonzo.Code.Once.Internal.Type.C_Float_36
      C_p'45'fmul_50 -> coe MAlonzo.Code.Once.Internal.Type.C_Float_36
      C_p'45'fdiv_52 -> coe MAlonzo.Code.Once.Internal.Type.C_Float_36
      C_p'45'i2f_54 -> coe MAlonzo.Code.Once.Internal.Type.C_Float_36
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.Syntax.Tm
d_Tm_62 a0 a1 a2 a3 = ()
data T_Tm_62
  = C_var_66 MAlonzo.Code.Data.Fin.Base.T_Fin_10 |
    C_lam_68 MAlonzo.Code.Once.Internal.Type.T_Type_8
             MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
             MAlonzo.Code.Once.Spec.Grade.T_Purity_40 T_Tm_62 |
    C_app_70 T_Tm_62 T_Tm_62 |
    C_let'8242'_72 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 T_Tm_62
                   T_Tm_62 |
    C_unit_74 | C_pair_76 T_Tm_62 T_Tm_62 | C_fst_78 T_Tm_62 |
    C_snd_80 T_Tm_62 |
    C_inl_82 MAlonzo.Code.Once.Internal.Type.T_Type_8 T_Tm_62 |
    C_inr_84 MAlonzo.Code.Once.Internal.Type.T_Type_8 T_Tm_62 |
    C_case_86 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
              MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 T_Tm_62 T_Tm_62 T_Tm_62 |
    C_absurd_88 MAlonzo.Code.Once.Internal.Type.T_Type_8 T_Tm_62 |
    C_roll_90 MAlonzo.Code.Once.Internal.Type.T_Functor_6 T_Tm_62 |
    C_fold_92 MAlonzo.Code.Once.Internal.Type.T_Functor_6 T_Tm_62
              T_Tm_62 |
    C_unfold_94 MAlonzo.Code.Once.Internal.Type.T_Functor_6 T_Tm_62
                T_Tm_62 |
    C_iter_96 T_Tm_62 T_Tm_62 | C_out_98 T_Tm_62 |
    C_coerce_100 MAlonzo.Code.Once.Internal.Type.T_Type_8
                 MAlonzo.Code.Once.Internal.Type.T_Type_8 T_Tm_62 |
    C_lit_102 T_Lit_14 | C_prim_104 T_Prim_20 T_Tm_62 |
    C_sigop_106 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
                MAlonzo.Code.Once.Internal.Type.T_Type_8 |
    C_ref_110 MAlonzo.Code.Data.Fin.Base.T_Fin_10
              (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
               MAlonzo.Code.Once.Internal.Type.T_Type_8)
-- Once.Internal.Core.Syntax.Ren
d_Ren_112 ::
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer -> Integer -> ()
d_Ren_112 = erased
-- Once.Internal.Core.Syntax.extR
d_extR_122 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_extR_122 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_extR_122 v5 v6
du_extR_122 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_extR_122 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe MAlonzo.Code.Data.Fin.Base.C_zero_12
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3
        -> coe MAlonzo.Code.Data.Fin.Base.C_suc_16 (coe v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.Syntax.ren
d_ren_134 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  T_Tm_62 -> T_Tm_62
d_ren_134 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_ren_134 v5 v6
du_ren_134 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  T_Tm_62 -> T_Tm_62
du_ren_134 v0 v1
  = case coe v1 of
      C_var_66 v2 -> coe C_var_66 (coe v0 v2)
      C_lam_68 v2 v3 v4 v5
        -> coe
             C_lam_68 (coe v2) (coe v3) (coe v4)
             (coe du_ren_134 (coe du_extR_122 (coe v0)) (coe v5))
      C_app_70 v2 v3
        -> coe
             C_app_70 (coe du_ren_134 (coe v0) (coe v2))
             (coe du_ren_134 (coe v0) (coe v3))
      C_let'8242'_72 v2 v3 v4
        -> coe
             C_let'8242'_72 (coe v2) (coe du_ren_134 (coe v0) (coe v3))
             (coe du_ren_134 (coe du_extR_122 (coe v0)) (coe v4))
      C_unit_74 -> coe v1
      C_pair_76 v2 v3
        -> coe
             C_pair_76 (coe du_ren_134 (coe v0) (coe v2))
             (coe du_ren_134 (coe v0) (coe v3))
      C_fst_78 v2 -> coe C_fst_78 (coe du_ren_134 (coe v0) (coe v2))
      C_snd_80 v2 -> coe C_snd_80 (coe du_ren_134 (coe v0) (coe v2))
      C_inl_82 v2 v3
        -> coe C_inl_82 (coe v2) (coe du_ren_134 (coe v0) (coe v3))
      C_inr_84 v2 v3
        -> coe C_inr_84 (coe v2) (coe du_ren_134 (coe v0) (coe v3))
      C_case_86 v2 v3 v4 v5 v6
        -> coe
             C_case_86 (coe v2) (coe v3) (coe du_ren_134 (coe v0) (coe v4))
             (coe du_ren_134 (coe du_extR_122 (coe v0)) (coe v5))
             (coe du_ren_134 (coe du_extR_122 (coe v0)) (coe v6))
      C_absurd_88 v2 v3
        -> coe C_absurd_88 (coe v2) (coe du_ren_134 (coe v0) (coe v3))
      C_roll_90 v2 v3
        -> coe C_roll_90 (coe v2) (coe du_ren_134 (coe v0) (coe v3))
      C_fold_92 v2 v3 v4
        -> coe
             C_fold_92 (coe v2) (coe du_ren_134 (coe v0) (coe v3))
             (coe du_ren_134 (coe v0) (coe v4))
      C_unfold_94 v2 v3 v4
        -> coe
             C_unfold_94 (coe v2) (coe du_ren_134 (coe v0) (coe v3))
             (coe du_ren_134 (coe v0) (coe v4))
      C_iter_96 v2 v3
        -> coe
             C_iter_96 (coe du_ren_134 (coe v0) (coe v2))
             (coe du_ren_134 (coe v0) (coe v3))
      C_out_98 v2 -> coe C_out_98 (coe du_ren_134 (coe v0) (coe v2))
      C_coerce_100 v2 v3 v4
        -> coe
             C_coerce_100 (coe v2) (coe v3) (coe du_ren_134 (coe v0) (coe v4))
      C_lit_102 v2 -> coe v1
      C_prim_104 v2 v3
        -> coe C_prim_104 (coe v2) (coe du_ren_134 (coe v0) (coe v3))
      C_sigop_106 v2 v3 -> coe v1
      C_ref_110 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.Syntax.wk
d_wk_274 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer -> T_Tm_62 -> T_Tm_62
d_wk_274 ~v0 ~v1 ~v2 ~v3 = du_wk_274
du_wk_274 :: T_Tm_62 -> T_Tm_62
du_wk_274
  = coe du_ren_134 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16)
-- Once.Internal.Core.Syntax.Sub
d_Sub_276 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer -> Integer -> ()
d_Sub_276 = erased
-- Once.Internal.Core.Syntax.extS
d_extS_286 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_62) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_62
d_extS_286 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_extS_286 v5 v6
du_extS_286 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_62) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_62
du_extS_286 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe C_var_66 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3 -> coe du_wk_274 (coe v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.Syntax.sub
d_sub_298 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_62) ->
  T_Tm_62 -> T_Tm_62
d_sub_298 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_sub_298 v5 v6
du_sub_298 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_62) ->
  T_Tm_62 -> T_Tm_62
du_sub_298 v0 v1
  = case coe v1 of
      C_var_66 v2 -> coe v0 v2
      C_lam_68 v2 v3 v4 v5
        -> coe
             C_lam_68 (coe v2) (coe v3) (coe v4)
             (coe du_sub_298 (coe du_extS_286 (coe v0)) (coe v5))
      C_app_70 v2 v3
        -> coe
             C_app_70 (coe du_sub_298 (coe v0) (coe v2))
             (coe du_sub_298 (coe v0) (coe v3))
      C_let'8242'_72 v2 v3 v4
        -> coe
             C_let'8242'_72 (coe v2) (coe du_sub_298 (coe v0) (coe v3))
             (coe du_sub_298 (coe du_extS_286 (coe v0)) (coe v4))
      C_unit_74 -> coe v1
      C_pair_76 v2 v3
        -> coe
             C_pair_76 (coe du_sub_298 (coe v0) (coe v2))
             (coe du_sub_298 (coe v0) (coe v3))
      C_fst_78 v2 -> coe C_fst_78 (coe du_sub_298 (coe v0) (coe v2))
      C_snd_80 v2 -> coe C_snd_80 (coe du_sub_298 (coe v0) (coe v2))
      C_inl_82 v2 v3
        -> coe C_inl_82 (coe v2) (coe du_sub_298 (coe v0) (coe v3))
      C_inr_84 v2 v3
        -> coe C_inr_84 (coe v2) (coe du_sub_298 (coe v0) (coe v3))
      C_case_86 v2 v3 v4 v5 v6
        -> coe
             C_case_86 (coe v2) (coe v3) (coe du_sub_298 (coe v0) (coe v4))
             (coe du_sub_298 (coe du_extS_286 (coe v0)) (coe v5))
             (coe du_sub_298 (coe du_extS_286 (coe v0)) (coe v6))
      C_absurd_88 v2 v3
        -> coe C_absurd_88 (coe v2) (coe du_sub_298 (coe v0) (coe v3))
      C_roll_90 v2 v3
        -> coe C_roll_90 (coe v2) (coe du_sub_298 (coe v0) (coe v3))
      C_fold_92 v2 v3 v4
        -> coe
             C_fold_92 (coe v2) (coe du_sub_298 (coe v0) (coe v3))
             (coe du_sub_298 (coe v0) (coe v4))
      C_unfold_94 v2 v3 v4
        -> coe
             C_unfold_94 (coe v2) (coe du_sub_298 (coe v0) (coe v3))
             (coe du_sub_298 (coe v0) (coe v4))
      C_iter_96 v2 v3
        -> coe
             C_iter_96 (coe du_sub_298 (coe v0) (coe v2))
             (coe du_sub_298 (coe v0) (coe v3))
      C_out_98 v2 -> coe C_out_98 (coe du_sub_298 (coe v0) (coe v2))
      C_coerce_100 v2 v3 v4
        -> coe
             C_coerce_100 (coe v2) (coe v3) (coe du_sub_298 (coe v0) (coe v4))
      C_lit_102 v2 -> coe v1
      C_prim_104 v2 v3
        -> coe C_prim_104 (coe v2) (coe du_sub_298 (coe v0) (coe v3))
      C_sigop_106 v2 v3 -> coe v1
      C_ref_110 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.Syntax.single
d_single_438 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  T_Tm_62 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_62
d_single_438 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_single_438 v4 v5
du_single_438 ::
  T_Tm_62 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_62
du_single_438 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v0
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3 -> coe C_var_66 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.Syntax._[_]
d__'91'_'93'_448 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer -> T_Tm_62 -> T_Tm_62 -> T_Tm_62
d__'91'_'93'_448 ~v0 ~v1 ~v2 ~v3 v4 v5 = du__'91'_'93'_448 v4 v5
du__'91'_'93'_448 :: T_Tm_62 -> T_Tm_62 -> T_Tm_62
du__'91'_'93'_448 v0 v1
  = coe du_sub_298 (coe du_single_438 (coe v1)) (coe v0)
-- Once.Internal.Core.Syntax.Value
d_Value_456 a0 a1 a2 a3 a4 = ()
data T_Value_456
  = C_v'45'var_462 | C_v'45'lam_472 | C_v'45'unit_474 |
    C_v'45'pair_480 T_Value_456 T_Value_456 |
    C_v'45'inl_486 T_Value_456 | C_v'45'inr_492 T_Value_456 |
    C_v'45'roll_498 T_Value_456
