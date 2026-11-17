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
import qualified MAlonzo.Code.Once.Spec.Theory
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
  = C_num_60 MAlonzo.Code.Once.Spec.Theory.T_NumTy_6
             MAlonzo.Code.Once.Spec.Theory.T_Theory_16
             MAlonzo.Code.Once.Spec.Theory.T_Shape_30
             MAlonzo.Code.Once.Spec.Theory.T_Has_104
             MAlonzo.Code.Once.Spec.Theory.T_Sym_38 |
    C_p'45'i2f_62
-- Once.Spec.Core.Syntax.primDom
d_primDom_66 ::
  Integer -> T_Prim_52 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_primDom_66 ~v0 v1 = du_primDom_66 v1
du_primDom_66 :: T_Prim_52 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_primDom_66 v0
  = case coe v0 of
      C_num_60 v1 v2 v3 v4 v5
        -> coe MAlonzo.Code.Once.Spec.Theory.du_symDom_86 (coe v1) (coe v3)
      C_p'45'i2f_62 -> coe MAlonzo.Code.Once.Spec.Type.C_Int_32
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Syntax.primCod
d_primCod_74 ::
  Integer -> T_Prim_52 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_primCod_74 ~v0 v1 = du_primCod_74 v1
du_primCod_74 :: T_Prim_52 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_primCod_74 v0
  = case coe v0 of
      C_num_60 v1 v2 v3 v4 v5
        -> coe MAlonzo.Code.Once.Spec.Theory.du_symCod_90 (coe v1) (coe v3)
      C_p'45'i2f_62 -> coe MAlonzo.Code.Once.Spec.Type.C_Float_34
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Syntax.Tm
d_Tm_86 a0 a1 a2 a3 = ()
data T_Tm_86
  = C_var_96 MAlonzo.Code.Data.Fin.Base.T_Fin_10 |
    C_lam_100 MAlonzo.Code.Once.Spec.Type.T_Ty_8
              MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
              MAlonzo.Code.Once.Spec.Grade.T_Purity_40 T_Tm_86 |
    C_app_104 T_Tm_86 T_Tm_86 |
    C_let'8242'_108 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 T_Tm_86
                    T_Tm_86 |
    C_unit_112 | C_pair_116 T_Tm_86 T_Tm_86 | C_fst_120 T_Tm_86 |
    C_snd_124 T_Tm_86 |
    C_inl_128 MAlonzo.Code.Once.Spec.Type.T_Ty_8 T_Tm_86 |
    C_inr_132 MAlonzo.Code.Once.Spec.Type.T_Ty_8 T_Tm_86 |
    C_case_136 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
               MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 T_Tm_86 T_Tm_86 T_Tm_86 |
    C_absurd_140 MAlonzo.Code.Once.Spec.Type.T_Ty_8 T_Tm_86 |
    C_roll_144 MAlonzo.Code.Once.Spec.Type.T_Fun_12 T_Tm_86 |
    C_fold_148 MAlonzo.Code.Once.Spec.Type.T_Fun_12 T_Tm_86 T_Tm_86 |
    C_unfold_152 MAlonzo.Code.Once.Spec.Type.T_Fun_12 T_Tm_86 T_Tm_86 |
    C_out_156 T_Tm_86 | C_iter_160 T_Tm_86 T_Tm_86 |
    C_coerce_164 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                 MAlonzo.Code.Once.Spec.Type.T_Ty_8 T_Tm_86 |
    C_lit_168 T_Lit_46 | C_prim_172 T_Prim_52 T_Tm_86 |
    C_sigop_176 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
                MAlonzo.Code.Once.Spec.Signature.T_DeclType_106 |
    C_ref_182 MAlonzo.Code.Data.Fin.Base.T_Fin_10
              (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
               MAlonzo.Code.Once.Spec.Type.T_Ty_8)
-- Once.Spec.Core.Syntax._.ext
d_ext_198 ::
  Integer ->
  T_Defs_24 ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_ext_198 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_ext_198 v5 v6
du_ext_198 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_ext_198 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe MAlonzo.Code.Data.Fin.Base.C_zero_12
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3
        -> coe MAlonzo.Code.Data.Fin.Base.C_suc_16 (coe v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Syntax._.ren
d_ren_210 ::
  Integer ->
  T_Defs_24 ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  T_Tm_86 -> T_Tm_86
d_ren_210 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_ren_210 v5 v6
du_ren_210 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  T_Tm_86 -> T_Tm_86
du_ren_210 v0 v1
  = case coe v1 of
      C_var_96 v3 -> coe C_var_96 (coe v0 v3)
      C_lam_100 v3 v4 v5 v6
        -> coe
             C_lam_100 v3 v4 v5
             (coe du_ren_210 (coe du_ext_198 (coe v0)) (coe v6))
      C_app_104 v3 v4
        -> coe
             C_app_104 (coe du_ren_210 (coe v0) (coe v3))
             (coe du_ren_210 (coe v0) (coe v4))
      C_let'8242'_108 v3 v4 v5
        -> coe
             C_let'8242'_108 v3 (coe du_ren_210 (coe v0) (coe v4))
             (coe du_ren_210 (coe du_ext_198 (coe v0)) (coe v5))
      C_unit_112 -> coe C_unit_112
      C_pair_116 v3 v4
        -> coe
             C_pair_116 (coe du_ren_210 (coe v0) (coe v3))
             (coe du_ren_210 (coe v0) (coe v4))
      C_fst_120 v3 -> coe C_fst_120 (coe du_ren_210 (coe v0) (coe v3))
      C_snd_124 v3 -> coe C_snd_124 (coe du_ren_210 (coe v0) (coe v3))
      C_inl_128 v3 v4
        -> coe C_inl_128 v3 (coe du_ren_210 (coe v0) (coe v4))
      C_inr_132 v3 v4
        -> coe C_inr_132 v3 (coe du_ren_210 (coe v0) (coe v4))
      C_case_136 v3 v4 v5 v6 v7
        -> coe
             C_case_136 v3 v4 (coe du_ren_210 (coe v0) (coe v5))
             (coe du_ren_210 (coe du_ext_198 (coe v0)) (coe v6))
             (coe du_ren_210 (coe du_ext_198 (coe v0)) (coe v7))
      C_absurd_140 v3 v4
        -> coe C_absurd_140 v3 (coe du_ren_210 (coe v0) (coe v4))
      C_roll_144 v3 v4
        -> coe C_roll_144 v3 (coe du_ren_210 (coe v0) (coe v4))
      C_fold_148 v3 v4 v5
        -> coe
             C_fold_148 v3 (coe du_ren_210 (coe v0) (coe v4))
             (coe du_ren_210 (coe v0) (coe v5))
      C_unfold_152 v3 v4 v5
        -> coe
             C_unfold_152 v3 (coe du_ren_210 (coe v0) (coe v4))
             (coe du_ren_210 (coe v0) (coe v5))
      C_out_156 v3 -> coe C_out_156 (coe du_ren_210 (coe v0) (coe v3))
      C_iter_160 v3 v4
        -> coe
             C_iter_160 (coe du_ren_210 (coe v0) (coe v3))
             (coe du_ren_210 (coe v0) (coe v4))
      C_coerce_164 v3 v4 v5
        -> coe C_coerce_164 v3 v4 (coe du_ren_210 (coe v0) (coe v5))
      C_lit_168 v3 -> coe C_lit_168 v3
      C_prim_172 v3 v4
        -> coe C_prim_172 v3 (coe du_ren_210 (coe v0) (coe v4))
      C_sigop_176 v3 v4 -> coe C_sigop_176 v3 v4
      C_ref_182 v3 v4 -> coe C_ref_182 v3 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Syntax._.wk
d_wk_350 ::
  Integer -> T_Defs_24 -> Integer -> Integer -> T_Tm_86 -> T_Tm_86
d_wk_350 ~v0 ~v1 ~v2 ~v3 = du_wk_350
du_wk_350 :: T_Tm_86 -> T_Tm_86
du_wk_350
  = coe du_ren_210 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16)
-- Once.Spec.Core.Syntax._.exts
d_exts_366 ::
  Integer ->
  T_Defs_24 ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_86) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_86
d_exts_366 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_exts_366 v5 v6
du_exts_366 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_86) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_86
du_exts_366 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe C_var_96 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3 -> coe du_wk_350 (coe v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Syntax._.subₜ
d_sub'8348'_378 ::
  Integer ->
  T_Defs_24 ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_86) ->
  T_Tm_86 -> T_Tm_86
d_sub'8348'_378 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_sub'8348'_378 v5 v6
du_sub'8348'_378 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Tm_86) ->
  T_Tm_86 -> T_Tm_86
du_sub'8348'_378 v0 v1
  = case coe v1 of
      C_var_96 v3 -> coe v0 v3
      C_lam_100 v3 v4 v5 v6
        -> coe
             C_lam_100 v3 v4 v5
             (coe du_sub'8348'_378 (coe du_exts_366 (coe v0)) (coe v6))
      C_app_104 v3 v4
        -> coe
             C_app_104 (coe du_sub'8348'_378 (coe v0) (coe v3))
             (coe du_sub'8348'_378 (coe v0) (coe v4))
      C_let'8242'_108 v3 v4 v5
        -> coe
             C_let'8242'_108 v3 (coe du_sub'8348'_378 (coe v0) (coe v4))
             (coe du_sub'8348'_378 (coe du_exts_366 (coe v0)) (coe v5))
      C_unit_112 -> coe C_unit_112
      C_pair_116 v3 v4
        -> coe
             C_pair_116 (coe du_sub'8348'_378 (coe v0) (coe v3))
             (coe du_sub'8348'_378 (coe v0) (coe v4))
      C_fst_120 v3
        -> coe C_fst_120 (coe du_sub'8348'_378 (coe v0) (coe v3))
      C_snd_124 v3
        -> coe C_snd_124 (coe du_sub'8348'_378 (coe v0) (coe v3))
      C_inl_128 v3 v4
        -> coe C_inl_128 v3 (coe du_sub'8348'_378 (coe v0) (coe v4))
      C_inr_132 v3 v4
        -> coe C_inr_132 v3 (coe du_sub'8348'_378 (coe v0) (coe v4))
      C_case_136 v3 v4 v5 v6 v7
        -> coe
             C_case_136 v3 v4 (coe du_sub'8348'_378 (coe v0) (coe v5))
             (coe du_sub'8348'_378 (coe du_exts_366 (coe v0)) (coe v6))
             (coe du_sub'8348'_378 (coe du_exts_366 (coe v0)) (coe v7))
      C_absurd_140 v3 v4
        -> coe C_absurd_140 v3 (coe du_sub'8348'_378 (coe v0) (coe v4))
      C_roll_144 v3 v4
        -> coe C_roll_144 v3 (coe du_sub'8348'_378 (coe v0) (coe v4))
      C_fold_148 v3 v4 v5
        -> coe
             C_fold_148 v3 (coe du_sub'8348'_378 (coe v0) (coe v4))
             (coe du_sub'8348'_378 (coe v0) (coe v5))
      C_unfold_152 v3 v4 v5
        -> coe
             C_unfold_152 v3 (coe du_sub'8348'_378 (coe v0) (coe v4))
             (coe du_sub'8348'_378 (coe v0) (coe v5))
      C_out_156 v3
        -> coe C_out_156 (coe du_sub'8348'_378 (coe v0) (coe v3))
      C_iter_160 v3 v4
        -> coe
             C_iter_160 (coe du_sub'8348'_378 (coe v0) (coe v3))
             (coe du_sub'8348'_378 (coe v0) (coe v4))
      C_coerce_164 v3 v4 v5
        -> coe C_coerce_164 v3 v4 (coe du_sub'8348'_378 (coe v0) (coe v5))
      C_lit_168 v3 -> coe C_lit_168 v3
      C_prim_172 v3 v4
        -> coe C_prim_172 v3 (coe du_sub'8348'_378 (coe v0) (coe v4))
      C_sigop_176 v3 v4 -> coe C_sigop_176 v3 v4
      C_ref_182 v3 v4 -> coe C_ref_182 v3 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Syntax._._[_]
d__'91'_'93'_518 ::
  Integer ->
  T_Defs_24 -> Integer -> Integer -> T_Tm_86 -> T_Tm_86 -> T_Tm_86
d__'91'_'93'_518 ~v0 ~v1 ~v2 ~v3 v4 v5 = du__'91'_'93'_518 v4 v5
du__'91'_'93'_518 :: T_Tm_86 -> T_Tm_86 -> T_Tm_86
du__'91'_'93'_518 v0 v1
  = coe
      du_sub'8348'_378
      (coe
         (\ v2 ->
            case coe v2 of
              MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v1
              MAlonzo.Code.Data.Fin.Base.C_suc_16 v4 -> coe C_var_96 v4
              _ -> MAlonzo.RTE.mazUnreachableError))
      (coe v0)
-- Once.Spec.Core.Syntax._⟪_⟫ₜ
d__'10218'_'10219''8348'_538 ::
  Integer ->
  T_Defs_24 ->
  Integer ->
  Integer ->
  Integer ->
  T_Tm_86 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  T_Tm_86
d__'10218'_'10219''8348'_538 ~v0 ~v1 v2 v3 ~v4 v5 v6
  = du__'10218'_'10219''8348'_538 v2 v3 v5 v6
du__'10218'_'10219''8348'_538 ::
  Integer ->
  Integer ->
  T_Tm_86 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  T_Tm_86
du__'10218'_'10219''8348'_538 v0 v1 v2 v3
  = case coe v2 of
      C_var_96 v5 -> coe C_var_96 v5
      C_lam_100 v5 v6 v7 v8
        -> coe
             C_lam_100
             (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'_154
                (coe v0) (coe v1) (coe v5) (coe v3))
             v6 v7
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v8) (coe v3))
      C_app_104 v5 v6
        -> coe
             C_app_104
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v6) (coe v3))
      C_let'8242'_108 v5 v6 v7
        -> coe
             C_let'8242'_108 v5
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v6) (coe v3))
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v7) (coe v3))
      C_unit_112 -> coe C_unit_112
      C_pair_116 v5 v6
        -> coe
             C_pair_116
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v6) (coe v3))
      C_fst_120 v5
        -> coe
             C_fst_120
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v5) (coe v3))
      C_snd_124 v5
        -> coe
             C_snd_124
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v5) (coe v3))
      C_inl_128 v5 v6
        -> coe
             C_inl_128
             (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'_154
                (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v6) (coe v3))
      C_inr_132 v5 v6
        -> coe
             C_inr_132
             (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'_154
                (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v6) (coe v3))
      C_case_136 v5 v6 v7 v8 v9
        -> coe
             C_case_136 v5 v6
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v7) (coe v3))
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v8) (coe v3))
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v9) (coe v3))
      C_absurd_140 v5 v6
        -> coe
             C_absurd_140
             (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'_154
                (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v6) (coe v3))
      C_roll_144 v5 v6
        -> coe
             C_roll_144
             (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'F_160
                (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v6) (coe v3))
      C_fold_148 v5 v6 v7
        -> coe
             C_fold_148
             (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'F_160
                (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v6) (coe v3))
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v7) (coe v3))
      C_unfold_152 v5 v6 v7
        -> coe
             C_unfold_152
             (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'F_160
                (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v6) (coe v3))
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v7) (coe v3))
      C_out_156 v5
        -> coe
             C_out_156
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v5) (coe v3))
      C_iter_160 v5 v6
        -> coe
             C_iter_160
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v6) (coe v3))
      C_coerce_164 v5 v6 v7
        -> coe
             C_coerce_164
             (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'_154
                (coe v0) (coe v1) (coe v5) (coe v3))
             (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'_154
                (coe v0) (coe v1) (coe v6) (coe v3))
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v7) (coe v3))
      C_lit_168 v5 -> coe C_lit_168 v5
      C_prim_172 v5 v6
        -> coe
             C_prim_172 v5
             (coe
                du__'10218'_'10219''8348'_538 (coe v0) (coe v1) (coe v6) (coe v3))
      C_sigop_176 v5 v6 -> coe C_sigop_176 v5 v6
      C_ref_182 v5 v6
        -> coe
             C_ref_182 v5
             (\ v7 ->
                MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'_154
                  (coe v0) (coe v1) (coe v6 v7) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
