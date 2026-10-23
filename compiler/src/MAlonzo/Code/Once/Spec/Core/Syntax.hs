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
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Signature
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Spec.Core.Syntax.Schema
d_Schema_8 = ()
data T_Schema_8
  = C_schema_22 Integer
                (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
                 MAlonzo.Code.Once.Spec.Type.T_Kind_70)
                MAlonzo.Code.Once.Spec.Type.T_Ty_8
-- Once.Spec.Core.Syntax.Schema.arity
d_arity_16 :: T_Schema_8 -> Integer
d_arity_16 v0
  = case coe v0 of
      C_schema_22 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Syntax.Schema.kinds
d_kinds_18 ::
  T_Schema_8 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Kind_70
d_kinds_18 v0
  = case coe v0 of
      C_schema_22 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Syntax.Schema.type
d_type_20 :: T_Schema_8 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_type_20 v0
  = case coe v0 of
      C_schema_22 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Syntax.Defs
d_Defs_24 a0 = ()
data T_Defs_24 = C_'91''93'_26 | C__'9655'__30 T_Defs_24 T_Schema_8
-- Once.Spec.Core.Syntax._!!_
d__'33''33'__34 ::
  Integer ->
  T_Defs_24 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Schema_8
d__'33''33'__34 ~v0 v1 v2 = du__'33''33'__34 v1 v2
du__'33''33'__34 ::
  T_Defs_24 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Schema_8
du__'33''33'__34 v0 v1
  = case coe v0 of
      C__'9655'__30 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v4
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v6
               -> coe du__'33''33'__34 (coe v3) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Syntax.Lit
d_Lit_46 = ()
data T_Lit_46
  = C_lit'45'int_48 Integer |
    C_lit'45'float_50 MAlonzo.Code.Once.Spec.Float.Decimal.T_Decimal_8
-- Once.Spec.Core.Syntax.Prim
d_Prim_52 = ()
data T_Prim_52
  = C_p'45'add_54 | C_p'45'sub_56 | C_p'45'mul_58 | C_p'45'div_60 |
    C_p'45'mod_62 | C_p'45'neg_64 | C_p'45'lt_66 | C_p'45'le_68 |
    C_p'45'gt_70 | C_p'45'ge_72 | C_p'45'eq_74 | C_p'45'ne_76 |
    C_p'45'fadd_78 | C_p'45'fsub_80 | C_p'45'fmul_82 | C_p'45'fdiv_84 |
    C_p'45'i2f_86
-- Once.Spec.Core.Syntax.primDom
d_primDom_90 ::
  Integer -> T_Prim_52 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_primDom_90 ~v0 v1 = du_primDom_90 v1
du_primDom_90 :: T_Prim_52 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_primDom_90 v0
  = case coe v0 of
      C_p'45'add_54
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      C_p'45'sub_56
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      C_p'45'mul_58
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      C_p'45'div_60
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      C_p'45'mod_62
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      C_p'45'neg_64 -> coe MAlonzo.Code.Once.Spec.Type.C_Int_32
      C_p'45'lt_66
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      C_p'45'le_68
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      C_p'45'gt_70
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      C_p'45'ge_72
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      C_p'45'eq_74
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      C_p'45'ne_76
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      C_p'45'fadd_78
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
             (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
      C_p'45'fsub_80
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
             (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
      C_p'45'fmul_82
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
             (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
      C_p'45'fdiv_84
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
             (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
      C_p'45'i2f_86 -> coe MAlonzo.Code.Once.Spec.Type.C_Int_32
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Syntax.primCod
d_primCod_94 ::
  Integer -> T_Prim_52 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_primCod_94 ~v0 v1 = du_primCod_94 v1
du_primCod_94 :: T_Prim_52 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_primCod_94 v0
  = case coe v0 of
      C_p'45'add_54 -> coe MAlonzo.Code.Once.Spec.Type.C_Int_32
      C_p'45'sub_56 -> coe MAlonzo.Code.Once.Spec.Type.C_Int_32
      C_p'45'mul_58 -> coe MAlonzo.Code.Once.Spec.Type.C_Int_32
      C_p'45'div_60 -> coe MAlonzo.Code.Once.Spec.Type.C_Int_32
      C_p'45'mod_62 -> coe MAlonzo.Code.Once.Spec.Type.C_Int_32
      C_p'45'neg_64 -> coe MAlonzo.Code.Once.Spec.Type.C_Int_32
      C_p'45'lt_66
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'43'__24
             (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
             (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
      C_p'45'le_68
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'43'__24
             (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
             (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
      C_p'45'gt_70
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'43'__24
             (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
             (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
      C_p'45'ge_72
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'43'__24
             (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
             (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
      C_p'45'eq_74
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'43'__24
             (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
             (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
      C_p'45'ne_76
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'43'__24
             (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
             (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
      C_p'45'fadd_78 -> coe MAlonzo.Code.Once.Spec.Type.C_Float_34
      C_p'45'fsub_80 -> coe MAlonzo.Code.Once.Spec.Type.C_Float_34
      C_p'45'fmul_82 -> coe MAlonzo.Code.Once.Spec.Type.C_Float_34
      C_p'45'fdiv_84 -> coe MAlonzo.Code.Once.Spec.Type.C_Float_34
      C_p'45'i2f_86 -> coe MAlonzo.Code.Once.Spec.Type.C_Float_34
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Syntax.Tm
d_Tm_102 a0 a1 a2 a3 = ()
data T_Tm_102
  = C_var_112 MAlonzo.Code.Data.Fin.Base.T_Fin_10 |
    C_lam_116 MAlonzo.Code.Once.Spec.Type.T_Ty_8
              MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
              MAlonzo.Code.Once.Spec.Grade.T_Purity_40 T_Tm_102 |
    C_app_120 T_Tm_102 T_Tm_102 |
    C_let'8242'_124 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 T_Tm_102
                    T_Tm_102 |
    C_unit_128 | C_pair_132 T_Tm_102 T_Tm_102 | C_fst_136 T_Tm_102 |
    C_snd_140 T_Tm_102 |
    C_inl_144 MAlonzo.Code.Once.Spec.Type.T_Ty_8 T_Tm_102 |
    C_inr_148 MAlonzo.Code.Once.Spec.Type.T_Ty_8 T_Tm_102 |
    C_case_152 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
               MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 T_Tm_102 T_Tm_102
               T_Tm_102 |
    C_absurd_156 MAlonzo.Code.Once.Spec.Type.T_Ty_8 T_Tm_102 |
    C_roll_160 MAlonzo.Code.Once.Spec.Type.T_Fun_12 T_Tm_102 |
    C_fold_164 MAlonzo.Code.Once.Spec.Type.T_Fun_12 T_Tm_102 T_Tm_102 |
    C_unfold_168 MAlonzo.Code.Once.Spec.Type.T_Fun_12 T_Tm_102
                 T_Tm_102 |
    C_out_172 T_Tm_102 | C_iter_176 T_Tm_102 T_Tm_102 |
    C_coerce_180 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                 MAlonzo.Code.Once.Spec.Type.T_Ty_8 T_Tm_102 |
    C_lit_184 T_Lit_46 | C_prim_188 T_Prim_52 T_Tm_102 |
    C_sigop_192 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
                MAlonzo.Code.Once.Spec.Signature.T_DeclType_106 |
    C_ref_198 MAlonzo.Code.Data.Fin.Base.T_Fin_10
              (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
               MAlonzo.Code.Once.Spec.Type.T_Ty_8)
-- Once.Spec.Core.Syntax._.ext
d_ext_214 ::
  Integer ->
  T_Defs_24 ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_ext_214 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_ext_214 v5 v6
du_ext_214 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_ext_214 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe MAlonzo.Code.Data.Fin.Base.C_zero_12
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3
        -> coe MAlonzo.Code.Data.Fin.Base.C_suc_16 (coe v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Syntax._.ren
d_ren_226 ::
  Integer ->
  T_Defs_24 ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  T_Tm_102 -> T_Tm_102
d_ren_226 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_ren_226 v5 v6
du_ren_226 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  T_Tm_102 -> T_Tm_102
du_ren_226 v0 v1
  = case coe v1 of
      C_var_112 v3 -> coe C_var_112 (coe v0 v3)
      C_lam_116 v3 v4 v5 v6
        -> coe
             C_lam_116 v3 v4 v5
             (coe du_ren_226 (coe du_ext_214 (coe v0)) (coe v6))
      C_app_120 v3 v4
        -> coe
             C_app_120 (coe du_ren_226 (coe v0) (coe v3))
             (coe du_ren_226 (coe v0) (coe v4))
      C_let'8242'_124 v3 v4 v5
        -> coe
             C_let'8242'_124 v3 (coe du_ren_226 (coe v0) (coe v4))
             (coe du_ren_226 (coe du_ext_214 (coe v0)) (coe v5))
      C_unit_128 -> coe C_unit_128
      C_pair_132 v3 v4
        -> coe
             C_pair_132 (coe du_ren_226 (coe v0) (coe v3))
             (coe du_ren_226 (coe v0) (coe v4))
      C_fst_136 v3 -> coe C_fst_136 (coe du_ren_226 (coe v0) (coe v3))
      C_snd_140 v3 -> coe C_snd_140 (coe du_ren_226 (coe v0) (coe v3))
      C_inl_144 v3 v4
        -> coe C_inl_144 v3 (coe du_ren_226 (coe v0) (coe v4))
      C_inr_148 v3 v4
        -> coe C_inr_148 v3 (coe du_ren_226 (coe v0) (coe v4))
      C_case_152 v3 v4 v5 v6 v7
        -> coe
             C_case_152 v3 v4 (coe du_ren_226 (coe v0) (coe v5))
             (coe du_ren_226 (coe du_ext_214 (coe v0)) (coe v6))
             (coe du_ren_226 (coe du_ext_214 (coe v0)) (coe v7))
      C_absurd_156 v3 v4
        -> coe C_absurd_156 v3 (coe du_ren_226 (coe v0) (coe v4))
      C_roll_160 v3 v4
        -> coe C_roll_160 v3 (coe du_ren_226 (coe v0) (coe v4))
      C_fold_164 v3 v4 v5
        -> coe
             C_fold_164 v3 (coe du_ren_226 (coe v0) (coe v4))
             (coe du_ren_226 (coe v0) (coe v5))
      C_unfold_168 v3 v4 v5
        -> coe
             C_unfold_168 v3 (coe du_ren_226 (coe v0) (coe v4))
             (coe du_ren_226 (coe v0) (coe v5))
      C_out_172 v3 -> coe C_out_172 (coe du_ren_226 (coe v0) (coe v3))
      C_iter_176 v3 v4
        -> coe
             C_iter_176 (coe du_ren_226 (coe v0) (coe v3))
             (coe du_ren_226 (coe v0) (coe v4))
      C_coerce_180 v3 v4 v5
        -> coe C_coerce_180 v3 v4 (coe du_ren_226 (coe v0) (coe v5))
      C_lit_184 v3 -> coe C_lit_184 v3
      C_prim_188 v3 v4
        -> coe C_prim_188 v3 (coe du_ren_226 (coe v0) (coe v4))
      C_sigop_192 v3 v4 -> coe C_sigop_192 v3 v4
      C_ref_198 v3 v4 -> coe C_ref_198 v3 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Syntax._.wk
d_wk_366 ::
  Integer -> T_Defs_24 -> Integer -> Integer -> T_Tm_102 -> T_Tm_102
d_wk_366 ~v0 ~v1 ~v2 ~v3 = du_wk_366
du_wk_366 :: T_Tm_102 -> T_Tm_102
du_wk_366
  = coe du_ren_226 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16)
-- Once.Spec.Core.Syntax._.exts
d_exts_382 ::
  Integer ->
  T_Defs_24 ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_102) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_102
d_exts_382 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_exts_382 v5 v6
du_exts_382 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_102) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_102
du_exts_382 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe C_var_112 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3 -> coe du_wk_366 (coe v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Syntax._.subₜ
d_sub'8348'_394 ::
  Integer ->
  T_Defs_24 ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_102) ->
  T_Tm_102 -> T_Tm_102
d_sub'8348'_394 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_sub'8348'_394 v5 v6
du_sub'8348'_394 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_102) ->
  T_Tm_102 -> T_Tm_102
du_sub'8348'_394 v0 v1
  = case coe v1 of
      C_var_112 v3 -> coe v0 v3
      C_lam_116 v3 v4 v5 v6
        -> coe
             C_lam_116 v3 v4 v5
             (coe du_sub'8348'_394 (coe du_exts_382 (coe v0)) (coe v6))
      C_app_120 v3 v4
        -> coe
             C_app_120 (coe du_sub'8348'_394 (coe v0) (coe v3))
             (coe du_sub'8348'_394 (coe v0) (coe v4))
      C_let'8242'_124 v3 v4 v5
        -> coe
             C_let'8242'_124 v3 (coe du_sub'8348'_394 (coe v0) (coe v4))
             (coe du_sub'8348'_394 (coe du_exts_382 (coe v0)) (coe v5))
      C_unit_128 -> coe C_unit_128
      C_pair_132 v3 v4
        -> coe
             C_pair_132 (coe du_sub'8348'_394 (coe v0) (coe v3))
             (coe du_sub'8348'_394 (coe v0) (coe v4))
      C_fst_136 v3
        -> coe C_fst_136 (coe du_sub'8348'_394 (coe v0) (coe v3))
      C_snd_140 v3
        -> coe C_snd_140 (coe du_sub'8348'_394 (coe v0) (coe v3))
      C_inl_144 v3 v4
        -> coe C_inl_144 v3 (coe du_sub'8348'_394 (coe v0) (coe v4))
      C_inr_148 v3 v4
        -> coe C_inr_148 v3 (coe du_sub'8348'_394 (coe v0) (coe v4))
      C_case_152 v3 v4 v5 v6 v7
        -> coe
             C_case_152 v3 v4 (coe du_sub'8348'_394 (coe v0) (coe v5))
             (coe du_sub'8348'_394 (coe du_exts_382 (coe v0)) (coe v6))
             (coe du_sub'8348'_394 (coe du_exts_382 (coe v0)) (coe v7))
      C_absurd_156 v3 v4
        -> coe C_absurd_156 v3 (coe du_sub'8348'_394 (coe v0) (coe v4))
      C_roll_160 v3 v4
        -> coe C_roll_160 v3 (coe du_sub'8348'_394 (coe v0) (coe v4))
      C_fold_164 v3 v4 v5
        -> coe
             C_fold_164 v3 (coe du_sub'8348'_394 (coe v0) (coe v4))
             (coe du_sub'8348'_394 (coe v0) (coe v5))
      C_unfold_168 v3 v4 v5
        -> coe
             C_unfold_168 v3 (coe du_sub'8348'_394 (coe v0) (coe v4))
             (coe du_sub'8348'_394 (coe v0) (coe v5))
      C_out_172 v3
        -> coe C_out_172 (coe du_sub'8348'_394 (coe v0) (coe v3))
      C_iter_176 v3 v4
        -> coe
             C_iter_176 (coe du_sub'8348'_394 (coe v0) (coe v3))
             (coe du_sub'8348'_394 (coe v0) (coe v4))
      C_coerce_180 v3 v4 v5
        -> coe C_coerce_180 v3 v4 (coe du_sub'8348'_394 (coe v0) (coe v5))
      C_lit_184 v3 -> coe C_lit_184 v3
      C_prim_188 v3 v4
        -> coe C_prim_188 v3 (coe du_sub'8348'_394 (coe v0) (coe v4))
      C_sigop_192 v3 v4 -> coe C_sigop_192 v3 v4
      C_ref_198 v3 v4 -> coe C_ref_198 v3 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Syntax._._[_]
d__'91'_'93'_534 ::
  Integer ->
  T_Defs_24 -> Integer -> Integer -> T_Tm_102 -> T_Tm_102 -> T_Tm_102
d__'91'_'93'_534 ~v0 ~v1 ~v2 ~v3 v4 v5 = du__'91'_'93'_534 v4 v5
du__'91'_'93'_534 :: T_Tm_102 -> T_Tm_102 -> T_Tm_102
du__'91'_'93'_534 v0 v1
  = coe
      du_sub'8348'_394
      (coe
         (\ v2 ->
            case coe v2 of
              MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v1
              MAlonzo.Code.Data.Fin.Base.C_suc_16 v4 -> coe C_var_112 v4
              _ -> MAlonzo.RTE.mazUnreachableError))
      (coe v0)
-- Once.Spec.Core.Syntax._⟪_⟫ₜ
d__'10218'_'10219''8348'_554 ::
  Integer ->
  T_Defs_24 ->
  Integer ->
  Integer ->
  Integer ->
  T_Tm_102 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  T_Tm_102
d__'10218'_'10219''8348'_554 ~v0 ~v1 v2 v3 ~v4 v5 v6
  = du__'10218'_'10219''8348'_554 v2 v3 v5 v6
du__'10218'_'10219''8348'_554 ::
  Integer ->
  Integer ->
  T_Tm_102 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  T_Tm_102
du__'10218'_'10219''8348'_554 v0 v1 v2 v3
  = case coe v2 of
      C_var_112 v5 -> coe C_var_112 v5
      C_lam_116 v5 v6 v7 v8
        -> coe
             C_lam_116
             (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'_154
                (coe v0) (coe v1) (coe v5) (coe v3))
             v6 v7
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v8) (coe v3))
      C_app_120 v5 v6
        -> coe
             C_app_120
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v6) (coe v3))
      C_let'8242'_124 v5 v6 v7
        -> coe
             C_let'8242'_124 v5
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v6) (coe v3))
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v7) (coe v3))
      C_unit_128 -> coe C_unit_128
      C_pair_132 v5 v6
        -> coe
             C_pair_132
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v6) (coe v3))
      C_fst_136 v5
        -> coe
             C_fst_136
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v5) (coe v3))
      C_snd_140 v5
        -> coe
             C_snd_140
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v5) (coe v3))
      C_inl_144 v5 v6
        -> coe
             C_inl_144
             (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'_154
                (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v6) (coe v3))
      C_inr_148 v5 v6
        -> coe
             C_inr_148
             (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'_154
                (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v6) (coe v3))
      C_case_152 v5 v6 v7 v8 v9
        -> coe
             C_case_152 v5 v6
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v7) (coe v3))
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v8) (coe v3))
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v9) (coe v3))
      C_absurd_156 v5 v6
        -> coe
             C_absurd_156
             (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'_154
                (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v6) (coe v3))
      C_roll_160 v5 v6
        -> coe
             C_roll_160
             (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'F_160
                (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v6) (coe v3))
      C_fold_164 v5 v6 v7
        -> coe
             C_fold_164
             (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'F_160
                (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v6) (coe v3))
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v7) (coe v3))
      C_unfold_168 v5 v6 v7
        -> coe
             C_unfold_168
             (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'F_160
                (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v6) (coe v3))
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v7) (coe v3))
      C_out_172 v5
        -> coe
             C_out_172
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v5) (coe v3))
      C_iter_176 v5 v6
        -> coe
             C_iter_176
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v6) (coe v3))
      C_coerce_180 v5 v6 v7
        -> coe
             C_coerce_180
             (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'_154
                (coe v0) (coe v1) (coe v5) (coe v3))
             (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'_154
                (coe v0) (coe v1) (coe v6) (coe v3))
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v7) (coe v3))
      C_lit_184 v5 -> coe C_lit_184 v5
      C_prim_188 v5 v6
        -> coe
             C_prim_188 v5
             (coe
                du__'10218'_'10219''8348'_554 (coe v0) (coe v1) (coe v6) (coe v3))
      C_sigop_192 v5 v6 -> coe C_sigop_192 v5 v6
      C_ref_198 v5 v6
        -> coe
             C_ref_198 v5
             (\ v7 ->
                MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'_154
                  (coe v0) (coe v1) (coe v6 v7) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
