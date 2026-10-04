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

module MAlonzo.Code.Once.Spec.Core.Derived where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Spec.Core.Syntax
import qualified MAlonzo.Code.Once.Type

-- Once.Spec.Core.Derived._.Tm
d_Tm_26 a0 a1 a2 a3 = ()
-- Once.Spec.Core.Derived.v0
d_v0_244 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_v0_244 ~v0 ~v1 = du_v0_244
du_v0_244 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_v0_244
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
-- Once.Spec.Core.Derived.v1
d_v1_248 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_v1_248 ~v0 ~v1 = du_v1_248
du_v1_248 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_v1_248
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
      (coe
         MAlonzo.Code.Data.Fin.Base.C_suc_16
         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
-- Once.Spec.Core.Derived.v2
d_v2_252 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_v2_252 ~v0 ~v1 = du_v2_252
du_v2_252 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_v2_252
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
      (coe
         MAlonzo.Code.Data.Fin.Base.C_suc_16
         (coe
            MAlonzo.Code.Data.Fin.Base.C_suc_16
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived.v3
d_v3_256 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_v3_256 ~v0 ~v1 = du_v3_256
du_v3_256 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_v3_256
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
      (coe
         MAlonzo.Code.Data.Fin.Base.C_suc_16
         (coe
            MAlonzo.Code.Data.Fin.Base.C_suc_16
            (coe
               MAlonzo.Code.Data.Fin.Base.C_suc_16
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
-- Once.Spec.Core.Derived.idᶜ
d_id'7580'_260 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_id'7580'_260 ~v0 ~v1 ~v2 ~v3 = du_id'7580'_260
du_id'7580'_260 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_id'7580'_260
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
-- Once.Spec.Core.Derived.fstᶜ
d_fst'7580'_264 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_fst'7580'_264 ~v0 ~v1 ~v2 ~v3 = du_fst'7580'_264
du_fst'7580'_264 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_fst'7580'_264
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_fst_78
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived.sndᶜ
d_snd'7580'_268 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_snd'7580'_268 ~v0 ~v1 ~v2 ~v3 = du_snd'7580'_268
du_snd'7580'_268 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_snd'7580'_268
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_snd_80
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived.inlᶜ
d_inl'7580'_272 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_inl'7580'_272 ~v0 ~v1 ~v2 ~v3 = du_inl'7580'_272
du_inl'7580'_272 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_inl'7580'_272
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_inl_82
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived.inrᶜ
d_inr'7580'_276 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_inr'7580'_276 ~v0 ~v1 ~v2 ~v3 = du_inr'7580'_276
du_inr'7580'_276 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_inr'7580'_276
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_inr_84
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived.terminalᶜ
d_terminal'7580'_280 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_terminal'7580'_280 ~v0 ~v1 ~v2 ~v3 = du_terminal'7580'_280
du_terminal'7580'_280 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_terminal'7580'_280
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
      (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_unit_74)
-- Once.Spec.Core.Derived.initialᶜ
d_initial'7580'_284 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_initial'7580'_284 ~v0 ~v1 ~v2 ~v3 = du_initial'7580'_284
du_initial'7580'_284 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_initial'7580'_284
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_absurd_88
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived.applyᶜ
d_apply'7580'_288 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_apply'7580'_288 ~v0 ~v1 ~v2 ~v3 = du_apply'7580'_288
du_apply'7580'_288 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_apply'7580'_288
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_app_70
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_fst_78
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_snd_80
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
-- Once.Spec.Core.Derived.inᶜ
d_in'7580'_292 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_in'7580'_292 ~v0 ~v1 ~v2 ~v3 = du_in'7580'_292
du_in'7580'_292 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_in'7580'_292
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_roll_90
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived.outᶜ
d_out'7580'_296 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_out'7580'_296 ~v0 ~v1 ~v2 ~v3 = du_out'7580'_296
du_out'7580'_296 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_out'7580'_296
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_out_96
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived.composeᶜ
d_compose'7580'_300 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_compose'7580'_300 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_compose'7580'_300 v4 v5
du_compose'7580'_300 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_compose'7580'_300 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_72 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_72
         (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_242 v1)
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_app_70
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_app_70
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.Spec.Core.Derived.pairᶜ
d_pair'7580'_308 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_pair'7580'_308 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_pair'7580'_308 v4 v5
du_pair'7580'_308 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_pair'7580'_308 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_72 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_72
         (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_242 v1)
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_pair_76
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_app_70
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_app_70
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.Spec.Core.Derived.caseᶜ
d_case'7580'_316 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_case'7580'_316 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_case'7580'_316 v4 v5
du_case'7580'_316 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_case'7580'_316 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_72 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_72
         (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_242 v1)
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_case_86
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_app_70
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_app_70
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.Spec.Core.Derived.curryᶜ
d_curry'7580'_324 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_curry'7580'_324 ~v0 ~v1 v2 = du_curry'7580'_324 v2
du_curry'7580'_324 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_curry'7580'_324 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_72 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_app_70
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_pair_76
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.Spec.Core.Derived.cataᶜ
d_cata'7580'_330 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_cata'7580'_330 ~v0 ~v1 ~v2 ~v3 v4 = du_cata'7580'_330 v4
du_cata'7580'_330 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_cata'7580'_330 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_72 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_fold_92
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
               (coe
                  MAlonzo.Code.Data.Fin.Base.C_suc_16
                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
-- Once.Spec.Core.Derived.anaᶜ
d_ana'7580'_334 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_ana'7580'_334 ~v0 ~v1 ~v2 ~v3 v4 = du_ana'7580'_334 v4
du_ana'7580'_334 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_ana'7580'_334 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_unfold_94
         (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_242 v0)
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived.effAppᶜ
d_effApp'7580'_342 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_effApp'7580'_342 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_effApp'7580'_342 v4 v5
du_effApp'7580'_342 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_effApp'7580'_342 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_app_70
         (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_242 v0)
         (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_242 v1))
-- Once.Spec.Core.Derived.seqᶜ
d_seq'7580'_350 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_seq'7580'_350 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_snd_80
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_pair_76 (coe v0) (coe v1))
-- Once.Spec.Core.Derived.applyEffᶜ
d_applyEff'7580'_358 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_applyEff'7580'_358 ~v0 ~v1 ~v2 ~v3 = du_applyEff'7580'_358
du_applyEff'7580'_358 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_applyEff'7580'_358
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_app_70
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_fst_78
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_snd_80
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.Spec.Core.Derived.outEffᶜ
d_outEff'7580'_362 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_outEff'7580'_362 ~v0 ~v1 ~v2 ~v3 = du_outEff'7580'_362
du_outEff'7580'_362 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_outEff'7580'_362
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_out_96
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
               (coe
                  MAlonzo.Code.Data.Fin.Base.C_suc_16
                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
-- Once.Spec.Core.Derived.mapᶜ
d_map'7580'_366 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_map'7580'_366 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_map'7580'_366 v4 v5 v6
du_map'7580'_366 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_map'7580'_366 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_112 v3 -> coe v2
      MAlonzo.Code.Once.Type.C_Id_114
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.du__'91'_'93'_386 (coe v1)
             (coe v2)
      MAlonzo.Code.Once.Type.C__'8853'__116 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_case_86 (coe v2)
             (coe
                MAlonzo.Code.Once.Spec.Core.Syntax.C_inl_82
                (coe
                   du_map'7580'_366 (coe v3)
                   (coe
                      MAlonzo.Code.Once.Spec.Core.Syntax.du_ren_132
                      (coe
                         MAlonzo.Code.Once.Spec.Core.Syntax.du_extR_120
                         (coe MAlonzo.Code.Data.Fin.Base.C_suc_16))
                      (coe v1))
                   (coe
                      MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
             (coe
                MAlonzo.Code.Once.Spec.Core.Syntax.C_inr_84
                (coe
                   du_map'7580'_366 (coe v4)
                   (coe
                      MAlonzo.Code.Once.Spec.Core.Syntax.du_ren_132
                      (coe
                         MAlonzo.Code.Once.Spec.Core.Syntax.du_extR_120
                         (coe MAlonzo.Code.Data.Fin.Base.C_suc_16))
                      (coe v1))
                   (coe
                      MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
      MAlonzo.Code.Once.Type.C__'8855'__118 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_72 (coe v2)
             (coe
                MAlonzo.Code.Once.Spec.Core.Syntax.C_pair_76
                (coe
                   du_map'7580'_366 (coe v3)
                   (coe
                      MAlonzo.Code.Once.Spec.Core.Syntax.du_ren_132
                      (coe
                         MAlonzo.Code.Once.Spec.Core.Syntax.du_extR_120
                         (coe MAlonzo.Code.Data.Fin.Base.C_suc_16))
                      (coe v1))
                   (coe
                      MAlonzo.Code.Once.Spec.Core.Syntax.C_fst_78
                      (coe
                         MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                (coe
                   du_map'7580'_366 (coe v4)
                   (coe
                      MAlonzo.Code.Once.Spec.Core.Syntax.du_ren_132
                      (coe
                         MAlonzo.Code.Once.Spec.Core.Syntax.du_extR_120
                         (coe MAlonzo.Code.Data.Fin.Base.C_suc_16))
                      (coe v1))
                   (coe
                      MAlonzo.Code.Once.Spec.Core.Syntax.C_snd_80
                      (coe
                         MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
      _ -> MAlonzo.RTE.mazUnreachableError
