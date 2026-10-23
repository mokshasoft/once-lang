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
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Spec.Core.Syntax
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Spec.Core.Derived._.v0
d_v0_20 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer -> Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_v0_20 ~v0 ~v1 ~v2 = du_v0_20
du_v0_20 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_v0_20
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
-- Once.Spec.Core.Derived._.v1
d_v1_24 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer -> Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_v1_24 ~v0 ~v1 ~v2 = du_v1_24
du_v1_24 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_v1_24
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
      (coe
         MAlonzo.Code.Data.Fin.Base.C_suc_16
         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
-- Once.Spec.Core.Derived._.v2
d_v2_28 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer -> Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_v2_28 ~v0 ~v1 ~v2 = du_v2_28
du_v2_28 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_v2_28
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
      (coe
         MAlonzo.Code.Data.Fin.Base.C_suc_16
         (coe
            MAlonzo.Code.Data.Fin.Base.C_suc_16
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived._.v3
d_v3_32 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer -> Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_v3_32 ~v0 ~v1 ~v2 = du_v3_32
du_v3_32 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_v3_32
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
      (coe
         MAlonzo.Code.Data.Fin.Base.C_suc_16
         (coe
            MAlonzo.Code.Data.Fin.Base.C_suc_16
            (coe
               MAlonzo.Code.Data.Fin.Base.C_suc_16
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
-- Once.Spec.Core.Derived._.idᶜ
d_id'7580'_36 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_id'7580'_36 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_id'7580'_36 v4 v5
du_id'7580'_36 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_id'7580'_36 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_116 v0
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v1
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
-- Once.Spec.Core.Derived._.terminalᶜ
d_terminal'7580'_40 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_terminal'7580'_40 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_terminal'7580'_40 v4 v5
du_terminal'7580'_40 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_terminal'7580'_40 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_116 v0
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v1
      (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_unit_128)
-- Once.Spec.Core.Derived._.initialᶜ
d_initial'7580'_44 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_initial'7580'_44 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_initial'7580'_44 v4 v5
du_initial'7580'_44 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_initial'7580'_44 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_116
      (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v1
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_absurd_156 v0
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived._.fstᶜ
d_fst'7580'_60 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_fst'7580'_60 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_fst'7580'_60 v4 v5 v6
du_fst'7580'_60 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_fst'7580'_60 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_116
      (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v0) (coe v1))
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v2
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_fst_136
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived._.sndᶜ
d_snd'7580'_64 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_snd'7580'_64 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_snd'7580'_64 v4 v5 v6
du_snd'7580'_64 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_snd'7580'_64 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_116
      (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v0) (coe v1))
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v2
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_snd_140
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived._.inlᶜ
d_inl'7580'_68 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_inl'7580'_68 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_inl'7580'_68 v4 v5 v6
du_inl'7580'_68 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_inl'7580'_68 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_116 v0
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v2
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_inl_144 v1
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived._.inrᶜ
d_inr'7580'_72 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_inr'7580'_72 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_inr'7580'_72 v4 v5 v6
du_inr'7580'_72 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_inr'7580'_72 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_116 v1
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v2
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_inr_148 v0
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived._.applyᶜ
d_apply'7580'_100 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_apply'7580'_100 ~v0 ~v1 ~v2 v3 v4 = du_apply'7580'_100 v3 v4
du_apply'7580'_100 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_apply'7580'_100 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_116
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'42'__22
         (coe
            MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v0)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
               (coe
                  MAlonzo.Code.Once.Spec.Grade.C_fin_42
                  (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
            (coe v1))
         (coe v0))
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
      (coe
         MAlonzo.Code.Once.Spec.Grade.C_fin_42
         (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_app_120
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_fst_136
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_snd_140
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
-- Once.Spec.Core.Derived._.inᶜ
d_in'7580'_108 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_in'7580'_108 ~v0 ~v1 ~v2 ~v3 v4 = du_in'7580'_108 v4
du_in'7580'_108 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_in'7580'_108 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_116
      (coe
         MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v0)
         (coe MAlonzo.Code.Once.Spec.Type.C_μ_28 (coe v0)))
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
      (coe
         MAlonzo.Code.Once.Spec.Grade.C_fin_42
         (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_roll_160 v0
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived._.outᶜ
d_out'7580'_112 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_out'7580'_112 ~v0 ~v1 ~v2 ~v3 v4 = du_out'7580'_112 v4
du_out'7580'_112 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_out'7580'_112 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_116
      (coe
         MAlonzo.Code.Once.Spec.Type.C_ν_30 (coe v0)
         (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
      (coe
         MAlonzo.Code.Once.Spec.Grade.C_fin_42
         (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_out_172
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived._.composeᶜ
d_compose'7580'_120 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_compose'7580'_120 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_compose'7580'_120 v4 v5 v6 v7
du_compose'7580'_120 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_compose'7580'_120 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_124
      (coe MAlonzo.Code.Once.Spec.Grade.C_One_10) v2
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_124
         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
         (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_366 v3)
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_116 v0
            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v1
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_app_120
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_app_120
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.Spec.Core.Derived._.pairᶜ
d_pair'7580'_132 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_pair'7580'_132 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_pair'7580'_132 v4 v5 v6 v7
du_pair'7580'_132 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_pair'7580'_132 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_124
      (coe MAlonzo.Code.Once.Spec.Grade.C_One_10) v2
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_124
         (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
         (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_366 v3)
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_116 v0
            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v1
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_pair_132
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_app_120
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_app_120
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.Spec.Core.Derived._.caseᶜ
d_case'7580'_144 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_case'7580'_144 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_case'7580'_144 v4 v5 v6 v7 v8
du_case'7580'_144 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_case'7580'_144 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_124
      (coe MAlonzo.Code.Once.Spec.Grade.C_One_10) v3
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_124
         (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
         (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_366 v4)
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_116
            (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v0) (coe v1))
            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v2
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_case_152
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_app_120
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_app_120
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.Spec.Core.Derived._.curryᶜ
d_curry'7580'_158 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_curry'7580'_158 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_curry'7580'_158 v3 v4 v5 v6 v7
du_curry'7580'_158 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_curry'7580'_158 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_124
      (coe MAlonzo.Code.Once.Spec.Grade.C_One_10) v4
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_116 v0
         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v2
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_116 v1
            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v3
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_app_120
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_pair_132
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.Spec.Core.Derived._.cataᶜ
d_cata'7580'_172 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_cata'7580'_172 ~v0 ~v1 ~v2 v3 v4 v5 = du_cata'7580'_172 v3 v4 v5
du_cata'7580'_172 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_cata'7580'_172 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_124
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v2
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_116
         (coe MAlonzo.Code.Once.Spec.Type.C_μ_28 (coe v0))
         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v1
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_fold_164 v0
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
               (coe
                  MAlonzo.Code.Data.Fin.Base.C_suc_16
                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
-- Once.Spec.Core.Derived._.loopᶜ
d_loop'7580'_182 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_loop'7580'_182 ~v0 ~v1 ~v2 v3 v4 = du_loop'7580'_182 v3 v4
du_loop'7580'_182 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_loop'7580'_182 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_124
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v1
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_116 v0
         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
         (coe MAlonzo.Code.Once.Spec.Grade.C_eff_44)
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_iter_176
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
               (coe
                  MAlonzo.Code.Data.Fin.Base.C_suc_16
                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
-- Once.Spec.Core.Derived._.anaᶜ
d_ana'7580'_190 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_ana'7580'_190 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_ana'7580'_190 v4 v5 v6 v7
du_ana'7580'_190 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_ana'7580'_190 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_116 v1
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v2
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_unfold_168 v0
         (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_366 v3)
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived._.effAppᶜ
d_effApp'7580'_202 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_effApp'7580'_202 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_effApp'7580'_202 v4 v5 v6
du_effApp'7580'_202 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_effApp'7580'_202 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_116
      (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v0
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_app_120
         (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_366 v1)
         (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_366 v2))
-- Once.Spec.Core.Derived._.applyEffᶜ
d_applyEff'7580'_212 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_applyEff'7580'_212 ~v0 ~v1 ~v2 v3 v4 v5
  = du_applyEff'7580'_212 v3 v4 v5
du_applyEff'7580'_212 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_applyEff'7580'_212 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_116
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'42'__22
         (coe
            MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v1)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v0))
            (coe v2))
         (coe v1))
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
      (coe
         MAlonzo.Code.Once.Spec.Grade.C_fin_42
         (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_116
         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v0
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_app_120
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_fst_136
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_snd_140
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.Spec.Core.Derived._.outActᶜ
d_outAct'7580'_222 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
d_outAct'7580'_222 ~v0 ~v1 ~v2 v3 = du_outAct'7580'_222 v3
du_outAct'7580'_222 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
du_outAct'7580'_222 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_116
      (coe
         MAlonzo.Code.Once.Spec.Type.C_ν_30 (coe v0)
         (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38))
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
      (coe
         MAlonzo.Code.Once.Spec.Grade.C_fin_42
         (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_116
         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
         (coe
            MAlonzo.Code.Once.Spec.Grade.C_fin_42
            (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38))
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_out_172
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_var_112
               (coe
                  MAlonzo.Code.Data.Fin.Base.C_suc_16
                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
