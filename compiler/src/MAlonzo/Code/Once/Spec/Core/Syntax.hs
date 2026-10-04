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

module MAlonzo.Code.Once.Spec.Core.Syntax where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Type

-- Once.Spec.Core.Syntax.Lit
d_Lit_14 a0 a1 a2 = ()
data T_Lit_14
  = C_lit'45'int_16 Integer |
    C_lit'45'float_18 MAlonzo.Code.Once.Float.Decimal.T_Decimal_6
-- Once.Spec.Core.Syntax.Prim
d_Prim_20 a0 a1 a2 = ()
data T_Prim_20
  = C_p'45'add_22 | C_p'45'sub_24 | C_p'45'mul_26 | C_p'45'div_28 |
    C_p'45'mod_30 | C_p'45'neg_32 | C_p'45'lt_34 | C_p'45'le_36 |
    C_p'45'gt_38 | C_p'45'ge_40 | C_p'45'eq_42 | C_p'45'ne_44 |
    C_p'45'fadd_46 | C_p'45'fsub_48 | C_p'45'fmul_50 | C_p'45'fdiv_52 |
    C_p'45'i2f_54
-- Once.Spec.Core.Syntax.primDom
d_primDom_56 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  T_Prim_20 -> MAlonzo.Code.Once.Type.T_Type_108
d_primDom_56 ~v0 ~v1 ~v2 v3 = du_primDom_56 v3
du_primDom_56 :: T_Prim_20 -> MAlonzo.Code.Once.Type.T_Type_108
du_primDom_56 v0
  = case coe v0 of
      C_p'45'add_22
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__124
             (coe MAlonzo.Code.Once.Type.C_Int_134)
             (coe MAlonzo.Code.Once.Type.C_Int_134)
      C_p'45'sub_24
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__124
             (coe MAlonzo.Code.Once.Type.C_Int_134)
             (coe MAlonzo.Code.Once.Type.C_Int_134)
      C_p'45'mul_26
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__124
             (coe MAlonzo.Code.Once.Type.C_Int_134)
             (coe MAlonzo.Code.Once.Type.C_Int_134)
      C_p'45'div_28
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__124
             (coe MAlonzo.Code.Once.Type.C_Int_134)
             (coe MAlonzo.Code.Once.Type.C_Int_134)
      C_p'45'mod_30
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__124
             (coe MAlonzo.Code.Once.Type.C_Int_134)
             (coe MAlonzo.Code.Once.Type.C_Int_134)
      C_p'45'neg_32 -> coe MAlonzo.Code.Once.Type.C_Int_134
      C_p'45'lt_34
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__124
             (coe MAlonzo.Code.Once.Type.C_Int_134)
             (coe MAlonzo.Code.Once.Type.C_Int_134)
      C_p'45'le_36
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__124
             (coe MAlonzo.Code.Once.Type.C_Int_134)
             (coe MAlonzo.Code.Once.Type.C_Int_134)
      C_p'45'gt_38
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__124
             (coe MAlonzo.Code.Once.Type.C_Int_134)
             (coe MAlonzo.Code.Once.Type.C_Int_134)
      C_p'45'ge_40
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__124
             (coe MAlonzo.Code.Once.Type.C_Int_134)
             (coe MAlonzo.Code.Once.Type.C_Int_134)
      C_p'45'eq_42
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__124
             (coe MAlonzo.Code.Once.Type.C_Int_134)
             (coe MAlonzo.Code.Once.Type.C_Int_134)
      C_p'45'ne_44
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__124
             (coe MAlonzo.Code.Once.Type.C_Int_134)
             (coe MAlonzo.Code.Once.Type.C_Int_134)
      C_p'45'fadd_46
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__124
             (coe MAlonzo.Code.Once.Type.C_Float_136)
             (coe MAlonzo.Code.Once.Type.C_Float_136)
      C_p'45'fsub_48
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__124
             (coe MAlonzo.Code.Once.Type.C_Float_136)
             (coe MAlonzo.Code.Once.Type.C_Float_136)
      C_p'45'fmul_50
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__124
             (coe MAlonzo.Code.Once.Type.C_Float_136)
             (coe MAlonzo.Code.Once.Type.C_Float_136)
      C_p'45'fdiv_52
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__124
             (coe MAlonzo.Code.Once.Type.C_Float_136)
             (coe MAlonzo.Code.Once.Type.C_Float_136)
      C_p'45'i2f_54 -> coe MAlonzo.Code.Once.Type.C_Int_134
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Syntax.primCod
d_primCod_58 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  T_Prim_20 -> MAlonzo.Code.Once.Type.T_Type_108
d_primCod_58 ~v0 ~v1 ~v2 v3 = du_primCod_58 v3
du_primCod_58 :: T_Prim_20 -> MAlonzo.Code.Once.Type.T_Type_108
du_primCod_58 v0
  = case coe v0 of
      C_p'45'add_22 -> coe MAlonzo.Code.Once.Type.C_Int_134
      C_p'45'sub_24 -> coe MAlonzo.Code.Once.Type.C_Int_134
      C_p'45'mul_26 -> coe MAlonzo.Code.Once.Type.C_Int_134
      C_p'45'div_28 -> coe MAlonzo.Code.Once.Type.C_Int_134
      C_p'45'mod_30 -> coe MAlonzo.Code.Once.Type.C_Int_134
      C_p'45'neg_32 -> coe MAlonzo.Code.Once.Type.C_Int_134
      C_p'45'lt_34
        -> coe
             MAlonzo.Code.Once.Type.C__'43'__126
             (coe MAlonzo.Code.Once.Type.C_Unit_120)
             (coe MAlonzo.Code.Once.Type.C_Unit_120)
      C_p'45'le_36
        -> coe
             MAlonzo.Code.Once.Type.C__'43'__126
             (coe MAlonzo.Code.Once.Type.C_Unit_120)
             (coe MAlonzo.Code.Once.Type.C_Unit_120)
      C_p'45'gt_38
        -> coe
             MAlonzo.Code.Once.Type.C__'43'__126
             (coe MAlonzo.Code.Once.Type.C_Unit_120)
             (coe MAlonzo.Code.Once.Type.C_Unit_120)
      C_p'45'ge_40
        -> coe
             MAlonzo.Code.Once.Type.C__'43'__126
             (coe MAlonzo.Code.Once.Type.C_Unit_120)
             (coe MAlonzo.Code.Once.Type.C_Unit_120)
      C_p'45'eq_42
        -> coe
             MAlonzo.Code.Once.Type.C__'43'__126
             (coe MAlonzo.Code.Once.Type.C_Unit_120)
             (coe MAlonzo.Code.Once.Type.C_Unit_120)
      C_p'45'ne_44
        -> coe
             MAlonzo.Code.Once.Type.C__'43'__126
             (coe MAlonzo.Code.Once.Type.C_Unit_120)
             (coe MAlonzo.Code.Once.Type.C_Unit_120)
      C_p'45'fadd_46 -> coe MAlonzo.Code.Once.Type.C_Float_136
      C_p'45'fsub_48 -> coe MAlonzo.Code.Once.Type.C_Float_136
      C_p'45'fmul_50 -> coe MAlonzo.Code.Once.Type.C_Float_136
      C_p'45'fdiv_52 -> coe MAlonzo.Code.Once.Type.C_Float_136
      C_p'45'i2f_54 -> coe MAlonzo.Code.Once.Type.C_Float_136
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Syntax.Tm
d_Tm_62 a0 a1 a2 a3 = ()
data T_Tm_62
  = C_var_66 MAlonzo.Code.Data.Fin.Base.T_Fin_10 | C_lam_68 T_Tm_62 |
    C_app_70 T_Tm_62 T_Tm_62 | C_let'8242'_72 T_Tm_62 T_Tm_62 |
    C_unit_74 | C_pair_76 T_Tm_62 T_Tm_62 | C_fst_78 T_Tm_62 |
    C_snd_80 T_Tm_62 | C_inl_82 T_Tm_62 | C_inr_84 T_Tm_62 |
    C_case_86 T_Tm_62 T_Tm_62 T_Tm_62 | C_absurd_88 T_Tm_62 |
    C_roll_90 T_Tm_62 | C_fold_92 T_Tm_62 T_Tm_62 |
    C_unfold_94 T_Tm_62 T_Tm_62 | C_out_96 T_Tm_62 |
    C_coerce_98 MAlonzo.Code.Once.Type.T_Type_108
                MAlonzo.Code.Once.Type.T_Type_108 T_Tm_62 |
    C_lit_100 T_Lit_14 | C_prim_102 T_Prim_20 T_Tm_62 |
    C_sigop_104 MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
                MAlonzo.Code.Once.Type.T_Type_108 |
    C_ref_108 MAlonzo.Code.Data.Fin.Base.T_Fin_10
              (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
               MAlonzo.Code.Once.Type.T_Type_108)
-- Once.Spec.Core.Syntax.Ren
d_Ren_110 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> Integer -> ()
d_Ren_110 = erased
-- Once.Spec.Core.Syntax.extR
d_extR_120 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_extR_120 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_extR_120 v5 v6
du_extR_120 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_extR_120 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe MAlonzo.Code.Data.Fin.Base.C_zero_12
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3
        -> coe MAlonzo.Code.Data.Fin.Base.C_suc_16 (coe v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Syntax.ren
d_ren_132 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  T_Tm_62 -> T_Tm_62
d_ren_132 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_ren_132 v5 v6
du_ren_132 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  T_Tm_62 -> T_Tm_62
du_ren_132 v0 v1
  = case coe v1 of
      C_var_66 v2 -> coe C_var_66 (coe v0 v2)
      C_lam_68 v2
        -> coe
             C_lam_68 (coe du_ren_132 (coe du_extR_120 (coe v0)) (coe v2))
      C_app_70 v2 v3
        -> coe
             C_app_70 (coe du_ren_132 (coe v0) (coe v2))
             (coe du_ren_132 (coe v0) (coe v3))
      C_let'8242'_72 v2 v3
        -> coe
             C_let'8242'_72 (coe du_ren_132 (coe v0) (coe v2))
             (coe du_ren_132 (coe du_extR_120 (coe v0)) (coe v3))
      C_unit_74 -> coe v1
      C_pair_76 v2 v3
        -> coe
             C_pair_76 (coe du_ren_132 (coe v0) (coe v2))
             (coe du_ren_132 (coe v0) (coe v3))
      C_fst_78 v2 -> coe C_fst_78 (coe du_ren_132 (coe v0) (coe v2))
      C_snd_80 v2 -> coe C_snd_80 (coe du_ren_132 (coe v0) (coe v2))
      C_inl_82 v2 -> coe C_inl_82 (coe du_ren_132 (coe v0) (coe v2))
      C_inr_84 v2 -> coe C_inr_84 (coe du_ren_132 (coe v0) (coe v2))
      C_case_86 v2 v3 v4
        -> coe
             C_case_86 (coe du_ren_132 (coe v0) (coe v2))
             (coe du_ren_132 (coe du_extR_120 (coe v0)) (coe v3))
             (coe du_ren_132 (coe du_extR_120 (coe v0)) (coe v4))
      C_absurd_88 v2
        -> coe C_absurd_88 (coe du_ren_132 (coe v0) (coe v2))
      C_roll_90 v2 -> coe C_roll_90 (coe du_ren_132 (coe v0) (coe v2))
      C_fold_92 v2 v3
        -> coe
             C_fold_92 (coe du_ren_132 (coe v0) (coe v2))
             (coe du_ren_132 (coe v0) (coe v3))
      C_unfold_94 v2 v3
        -> coe
             C_unfold_94 (coe du_ren_132 (coe v0) (coe v2))
             (coe du_ren_132 (coe v0) (coe v3))
      C_out_96 v2 -> coe C_out_96 (coe du_ren_132 (coe v0) (coe v2))
      C_coerce_98 v2 v3 v4
        -> coe
             C_coerce_98 (coe v2) (coe v3) (coe du_ren_132 (coe v0) (coe v4))
      C_lit_100 v2 -> coe v1
      C_prim_102 v2 v3
        -> coe C_prim_102 (coe v2) (coe du_ren_132 (coe v0) (coe v3))
      C_sigop_104 v2 v3 -> coe v1
      C_ref_108 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Syntax.wk
d_wk_242 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> T_Tm_62 -> T_Tm_62
d_wk_242 ~v0 ~v1 ~v2 ~v3 = du_wk_242
du_wk_242 :: T_Tm_62 -> T_Tm_62
du_wk_242
  = coe du_ren_132 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16)
-- Once.Spec.Core.Syntax.Sub
d_Sub_244 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> Integer -> ()
d_Sub_244 = erased
-- Once.Spec.Core.Syntax.extS
d_extS_254 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_62) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_62
d_extS_254 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_extS_254 v5 v6
du_extS_254 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_62) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_62
du_extS_254 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe C_var_66 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3 -> coe du_wk_242 (coe v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Syntax.sub
d_sub_266 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_62) ->
  T_Tm_62 -> T_Tm_62
d_sub_266 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_sub_266 v5 v6
du_sub_266 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_62) ->
  T_Tm_62 -> T_Tm_62
du_sub_266 v0 v1
  = case coe v1 of
      C_var_66 v2 -> coe v0 v2
      C_lam_68 v2
        -> coe
             C_lam_68 (coe du_sub_266 (coe du_extS_254 (coe v0)) (coe v2))
      C_app_70 v2 v3
        -> coe
             C_app_70 (coe du_sub_266 (coe v0) (coe v2))
             (coe du_sub_266 (coe v0) (coe v3))
      C_let'8242'_72 v2 v3
        -> coe
             C_let'8242'_72 (coe du_sub_266 (coe v0) (coe v2))
             (coe du_sub_266 (coe du_extS_254 (coe v0)) (coe v3))
      C_unit_74 -> coe v1
      C_pair_76 v2 v3
        -> coe
             C_pair_76 (coe du_sub_266 (coe v0) (coe v2))
             (coe du_sub_266 (coe v0) (coe v3))
      C_fst_78 v2 -> coe C_fst_78 (coe du_sub_266 (coe v0) (coe v2))
      C_snd_80 v2 -> coe C_snd_80 (coe du_sub_266 (coe v0) (coe v2))
      C_inl_82 v2 -> coe C_inl_82 (coe du_sub_266 (coe v0) (coe v2))
      C_inr_84 v2 -> coe C_inr_84 (coe du_sub_266 (coe v0) (coe v2))
      C_case_86 v2 v3 v4
        -> coe
             C_case_86 (coe du_sub_266 (coe v0) (coe v2))
             (coe du_sub_266 (coe du_extS_254 (coe v0)) (coe v3))
             (coe du_sub_266 (coe du_extS_254 (coe v0)) (coe v4))
      C_absurd_88 v2
        -> coe C_absurd_88 (coe du_sub_266 (coe v0) (coe v2))
      C_roll_90 v2 -> coe C_roll_90 (coe du_sub_266 (coe v0) (coe v2))
      C_fold_92 v2 v3
        -> coe
             C_fold_92 (coe du_sub_266 (coe v0) (coe v2))
             (coe du_sub_266 (coe v0) (coe v3))
      C_unfold_94 v2 v3
        -> coe
             C_unfold_94 (coe du_sub_266 (coe v0) (coe v2))
             (coe du_sub_266 (coe v0) (coe v3))
      C_out_96 v2 -> coe C_out_96 (coe du_sub_266 (coe v0) (coe v2))
      C_coerce_98 v2 v3 v4
        -> coe
             C_coerce_98 (coe v2) (coe v3) (coe du_sub_266 (coe v0) (coe v4))
      C_lit_100 v2 -> coe v1
      C_prim_102 v2 v3
        -> coe C_prim_102 (coe v2) (coe du_sub_266 (coe v0) (coe v3))
      C_sigop_104 v2 v3 -> coe v1
      C_ref_108 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Syntax.single
d_single_376 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  T_Tm_62 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_62
d_single_376 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_single_376 v4 v5
du_single_376 ::
  T_Tm_62 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_62
du_single_376 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v0
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3 -> coe C_var_66 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Syntax._[_]
d__'91'_'93'_386 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> T_Tm_62 -> T_Tm_62 -> T_Tm_62
d__'91'_'93'_386 ~v0 ~v1 ~v2 ~v3 v4 v5 = du__'91'_'93'_386 v4 v5
du__'91'_'93'_386 :: T_Tm_62 -> T_Tm_62 -> T_Tm_62
du__'91'_'93'_386 v0 v1
  = coe du_sub_266 (coe du_single_376 (coe v1)) (coe v0)
-- Once.Spec.Core.Syntax.Value
d_Value_394 a0 a1 a2 a3 a4 = ()
data T_Value_394
  = C_v'45'var_400 | C_v'45'lam_404 | C_v'45'unit_406 |
    C_v'45'pair_412 T_Value_394 T_Value_394 |
    C_v'45'inl_416 T_Value_394 | C_v'45'inr_420 T_Value_394 |
    C_v'45'roll_424 T_Value_394
