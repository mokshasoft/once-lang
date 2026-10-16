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

module MAlonzo.Code.Once.Lang.Core.Derived where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Lang.Core.PolyTy
import qualified MAlonzo.Code.Once.Lang.Core.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Spec.Name

-- Once.Lang.Core.Derived._.Tm
d_Tm_26 a0 a1 a2 a3 = ()
-- Once.Lang.Core.Derived.v0
d_v0_248 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer -> MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_v0_248 ~v0 ~v1 = du_v0_248
du_v0_248 :: MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_v0_248
  = coe
      MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
-- Once.Lang.Core.Derived.v1
d_v1_252 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer -> MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_v1_252 ~v0 ~v1 = du_v1_252
du_v1_252 :: MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_v1_252
  = coe
      MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
      (coe
         MAlonzo.Code.Data.Fin.Base.C_suc_16
         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
-- Once.Lang.Core.Derived.v2
d_v2_256 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer -> MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_v2_256 ~v0 ~v1 = du_v2_256
du_v2_256 :: MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_v2_256
  = coe
      MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
      (coe
         MAlonzo.Code.Data.Fin.Base.C_suc_16
         (coe
            MAlonzo.Code.Data.Fin.Base.C_suc_16
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Lang.Core.Derived.v3
d_v3_260 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer -> MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_v3_260 ~v0 ~v1 = du_v3_260
du_v3_260 :: MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_v3_260
  = coe
      MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
      (coe
         MAlonzo.Code.Data.Fin.Base.C_suc_16
         (coe
            MAlonzo.Code.Data.Fin.Base.C_suc_16
            (coe
               MAlonzo.Code.Data.Fin.Base.C_suc_16
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
-- Once.Lang.Core.Derived.idᶜ
d_id'7580'_264 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_id'7580'_264 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_id'7580'_264 v4 v5
du_id'7580'_264 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_id'7580'_264 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68 (coe v0)
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1)
      (coe
         MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
-- Once.Lang.Core.Derived.terminalᶜ
d_terminal'7580'_268 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_terminal'7580'_268 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_terminal'7580'_268 v4 v5
du_terminal'7580'_268 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_terminal'7580'_268 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68 (coe v0)
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1)
      (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_unit_74)
-- Once.Lang.Core.Derived.fstᶜ
d_fst'7580'_280 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_fst'7580'_280 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_fst'7580'_280 v4 v5 v6
du_fst'7580'_280 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_fst'7580'_280 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
      (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v0) (coe v1))
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v2)
      (coe
         MAlonzo.Code.Once.Lang.Core.Syntax.C_fst_78
         (coe
            MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Lang.Core.Derived.sndᶜ
d_snd'7580'_284 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_snd'7580'_284 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_snd'7580'_284 v4 v5 v6
du_snd'7580'_284 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_snd'7580'_284 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
      (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v0) (coe v1))
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v2)
      (coe
         MAlonzo.Code.Once.Lang.Core.Syntax.C_snd_80
         (coe
            MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Lang.Core.Derived.inlᶜ
d_inl'7580'_288 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_inl'7580'_288 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_inl'7580'_288 v4 v5 v6
du_inl'7580'_288 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_inl'7580'_288 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68 (coe v0)
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v2)
      (coe
         MAlonzo.Code.Once.Lang.Core.Syntax.C_inl_82 (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Lang.Core.Derived.inrᶜ
d_inr'7580'_292 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_inr'7580'_292 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_inr'7580'_292 v4 v5 v6
du_inr'7580'_292 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_inr'7580'_292 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68 (coe v1)
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v2)
      (coe
         MAlonzo.Code.Once.Lang.Core.Syntax.C_inr_84 (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Lang.Core.Derived.initialᶜ
d_initial'7580'_320 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_initial'7580'_320 ~v0 ~v1 v2 v3 = du_initial'7580'_320 v2 v3
du_initial'7580'_320 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_initial'7580'_320 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
      (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1)
      (coe
         MAlonzo.Code.Once.Lang.Core.Syntax.C_absurd_88 (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Lang.Core.Derived.applyᶜ
d_apply'7580'_328 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_apply'7580'_328 ~v0 ~v1 v2 v3 = du_apply'7580'_328 v2 v3
du_apply'7580'_328 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_apply'7580'_328 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'42'__24
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v0)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
            (coe v1))
         (coe v0))
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
      (coe
         MAlonzo.Code.Once.Lang.Core.Syntax.C_app_70
         (coe
            MAlonzo.Code.Once.Lang.Core.Syntax.C_fst_78
            (coe
               MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
         (coe
            MAlonzo.Code.Once.Lang.Core.Syntax.C_snd_80
            (coe
               MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
-- Once.Lang.Core.Derived.inᶜ
d_in'7580'_336 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_in'7580'_336 ~v0 ~v1 ~v2 ~v3 v4 = du_in'7580'_336 v4
du_in'7580'_336 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_in'7580'_336 v0
  = coe
      MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
      (coe
         MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v0)
         (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v0)))
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
      (coe
         MAlonzo.Code.Once.Lang.Core.Syntax.C_roll_90 (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Lang.Core.Derived.outᶜ
d_out'7580'_340 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_out'7580'_340 ~v0 ~v1 ~v2 ~v3 v4 = du_out'7580'_340 v4
du_out'7580'_340 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_out'7580'_340 v0
  = coe
      MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
      (coe
         MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v0)
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
      (coe
         MAlonzo.Code.Once.Lang.Core.Syntax.C_out_98
         (coe
            MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Lang.Core.Derived.composeᶜ
d_compose'7580'_348 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_compose'7580'_348 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_compose'7580'_348 v4 v5 v6 v7
du_compose'7580'_348 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_compose'7580'_348 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Core.Syntax.C_let'8242'_72
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12) (coe v2)
      (coe
         MAlonzo.Code.Once.Lang.Core.Syntax.C_let'8242'_72
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
         (coe MAlonzo.Code.Once.Lang.Core.Syntax.du_wk_274 v3)
         (coe
            MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68 (coe v0)
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1)
            (coe
               MAlonzo.Code.Once.Lang.Core.Syntax.C_app_70
               (coe
                  MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
               (coe
                  MAlonzo.Code.Once.Lang.Core.Syntax.C_app_70
                  (coe
                     MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.Lang.Core.Derived.pairᶜ
d_pair'7580'_360 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_pair'7580'_360 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_pair'7580'_360 v4 v5 v6 v7
du_pair'7580'_360 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_pair'7580'_360 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Core.Syntax.C_let'8242'_72
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12) (coe v2)
      (coe
         MAlonzo.Code.Once.Lang.Core.Syntax.C_let'8242'_72
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
         (coe MAlonzo.Code.Once.Lang.Core.Syntax.du_wk_274 v3)
         (coe
            MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68 (coe v0)
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1)
            (coe
               MAlonzo.Code.Once.Lang.Core.Syntax.C_pair_76
               (coe
                  MAlonzo.Code.Once.Lang.Core.Syntax.C_app_70
                  (coe
                     MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                  (coe
                     MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
               (coe
                  MAlonzo.Code.Once.Lang.Core.Syntax.C_app_70
                  (coe
                     MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.Lang.Core.Derived.caseᶜ
d_case'7580'_372 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_case'7580'_372 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_case'7580'_372 v4 v5 v6 v7 v8
du_case'7580'_372 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_case'7580'_372 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Lang.Core.Syntax.C_let'8242'_72
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12) (coe v3)
      (coe
         MAlonzo.Code.Once.Lang.Core.Syntax.C_let'8242'_72
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
         (coe MAlonzo.Code.Once.Lang.Core.Syntax.du_wk_274 v4)
         (coe
            MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
            (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v0) (coe v1))
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v2)
            (coe
               MAlonzo.Code.Once.Lang.Core.Syntax.C_case_86
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
               (coe
                  MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
               (coe
                  MAlonzo.Code.Once.Lang.Core.Syntax.C_app_70
                  (coe
                     MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                  (coe
                     MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
               (coe
                  MAlonzo.Code.Once.Lang.Core.Syntax.C_app_70
                  (coe
                     MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                  (coe
                     MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.Lang.Core.Derived.curryᶜ
d_curry'7580'_386 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_curry'7580'_386 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_curry'7580'_386 v2 v3 v4 v5 v6
du_curry'7580'_386 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_curry'7580'_386 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Lang.Core.Syntax.C_let'8242'_72
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12) (coe v4)
      (coe
         MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68 (coe v0)
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v2)
         (coe
            MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68 (coe v1)
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v3)
            (coe
               MAlonzo.Code.Once.Lang.Core.Syntax.C_app_70
               (coe
                  MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
               (coe
                  MAlonzo.Code.Once.Lang.Core.Syntax.C_pair_76
                  (coe
                     MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.Lang.Core.Derived.cataᶜ
d_cata'7580'_400 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_cata'7580'_400 ~v0 ~v1 v2 v3 v4 = du_cata'7580'_400 v2 v3 v4
du_cata'7580'_400 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_cata'7580'_400 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Core.Syntax.C_let'8242'_72
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v2)
      (coe
         MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
         (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v0))
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Core.Syntax.C_fold_92 (coe v0)
            (coe
               MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
               (coe
                  MAlonzo.Code.Data.Fin.Base.C_suc_16
                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
            (coe
               MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
-- Once.Lang.Core.Derived.anaᶜ
d_ana'7580'_410 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_ana'7580'_410 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_ana'7580'_410 v4 v5 v6 v7
du_ana'7580'_410 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_ana'7580'_410 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68 (coe v1)
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v2)
      (coe
         MAlonzo.Code.Once.Lang.Core.Syntax.C_unfold_94 (coe v0)
         (coe MAlonzo.Code.Once.Lang.Core.Syntax.du_wk_274 v3)
         (coe
            MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Lang.Core.Derived.effAppᶜ
d_effApp'7580'_422 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_effApp'7580'_422 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_effApp'7580'_422 v4 v5 v6
du_effApp'7580'_422 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_effApp'7580'_422 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
      (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v0)
      (coe
         MAlonzo.Code.Once.Lang.Core.Syntax.C_app_70
         (coe MAlonzo.Code.Once.Lang.Core.Syntax.du_wk_274 v1)
         (coe MAlonzo.Code.Once.Lang.Core.Syntax.du_wk_274 v2))
-- Once.Lang.Core.Derived.applyEffᶜ
d_applyEff'7580'_432 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_applyEff'7580'_432 ~v0 ~v1 v2 v3 v4
  = du_applyEff'7580'_432 v2 v3 v4
du_applyEff'7580'_432 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_applyEff'7580'_432 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'42'__24
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v1)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v0))
            (coe v2))
         (coe v1))
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
      (coe
         MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Core.Syntax.C_app_70
            (coe
               MAlonzo.Code.Once.Lang.Core.Syntax.C_fst_78
               (coe
                  MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
            (coe
               MAlonzo.Code.Once.Lang.Core.Syntax.C_snd_80
               (coe
                  MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.Lang.Core.Derived.outEffᶜ
d_outEff'7580'_442 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_outEff'7580'_442 ~v0 ~v1 v2 v3 = du_outEff'7580'_442 v2 v3
du_outEff'7580'_442 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_outEff'7580'_442 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
      (coe MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v1) (coe v0))
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
      (coe
         MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Core.Syntax.C_out_98
            (coe
               MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
               (coe
                  MAlonzo.Code.Data.Fin.Base.C_suc_16
                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
