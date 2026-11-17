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

-- Once.Spec.Core.Derived.𝕋
d_𝕋_10 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_𝕋_10 ~v0 v1 v2 = du_𝕋_10 v1 v2
du_𝕋_10 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_𝕋_10 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v2
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36 -> coe v1
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                    (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v0))
                    (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
             (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
             (coe
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v0))
             (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Derived._.v0
d_v0_30 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer -> Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_v0_30 ~v0 ~v1 ~v2 = du_v0_30
du_v0_30 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_v0_30
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
-- Once.Spec.Core.Derived._.v1
d_v1_34 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer -> Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_v1_34 ~v0 ~v1 ~v2 = du_v1_34
du_v1_34 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_v1_34
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
      (coe
         MAlonzo.Code.Data.Fin.Base.C_suc_16
         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
-- Once.Spec.Core.Derived._.v2
d_v2_38 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer -> Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_v2_38 ~v0 ~v1 ~v2 = du_v2_38
du_v2_38 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_v2_38
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
      (coe
         MAlonzo.Code.Data.Fin.Base.C_suc_16
         (coe
            MAlonzo.Code.Data.Fin.Base.C_suc_16
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived._.v3
d_v3_42 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer -> Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_v3_42 ~v0 ~v1 ~v2 = du_v3_42
du_v3_42 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_v3_42
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
      (coe
         MAlonzo.Code.Data.Fin.Base.C_suc_16
         (coe
            MAlonzo.Code.Data.Fin.Base.C_suc_16
            (coe
               MAlonzo.Code.Data.Fin.Base.C_suc_16
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
-- Once.Spec.Core.Derived._.idᶜ
d_id'7580'_46 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_id'7580'_46 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_id'7580'_46 v4 v5
du_id'7580'_46 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_id'7580'_46 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100 v0
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v1
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
-- Once.Spec.Core.Derived._.terminalᶜ
d_terminal'7580'_50 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_terminal'7580'_50 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_terminal'7580'_50 v4 v5
du_terminal'7580'_50 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_terminal'7580'_50 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100 v0
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v1
      (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_unit_112)
-- Once.Spec.Core.Derived._.initialᶜ
d_initial'7580'_54 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_initial'7580'_54 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_initial'7580'_54 v4 v5
du_initial'7580'_54 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_initial'7580'_54 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
      (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v1
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_absurd_140 v0
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived._.toFloatᶜ
d_toFloat'7580'_70 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer -> Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_toFloat'7580'_70 ~v0 ~v1 ~v2 = du_toFloat'7580'_70
du_toFloat'7580'_70 :: MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_toFloat'7580'_70
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
      (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
      (coe
         MAlonzo.Code.Once.Spec.Grade.C_fin_42
         (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_prim_172
         (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'i2f_62)
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived._.fstᶜ
d_fst'7580'_74 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_fst'7580'_74 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_fst'7580'_74 v4 v5 v6
du_fst'7580'_74 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_fst'7580'_74 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
      (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v0) (coe v1))
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v2
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_fst_120
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived._.sndᶜ
d_snd'7580'_78 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_snd'7580'_78 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_snd'7580'_78 v4 v5 v6
du_snd'7580'_78 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_snd'7580'_78 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
      (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v0) (coe v1))
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v2
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_snd_124
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived._.inlᶜ
d_inl'7580'_82 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_inl'7580'_82 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_inl'7580'_82 v4 v5 v6
du_inl'7580'_82 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_inl'7580'_82 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100 v0
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v2
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_inl_128 v1
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived._.inrᶜ
d_inr'7580'_86 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_inr'7580'_86 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_inr'7580'_86 v4 v5 v6
du_inr'7580'_86 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_inr'7580'_86 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100 v1
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v2
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_inr_132 v0
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived._.applyᶜ
d_apply'7580'_114 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_apply'7580'_114 ~v0 ~v1 ~v2 v3 v4 v5
  = du_apply'7580'_114 v3 v4 v5
du_apply'7580'_114 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_apply'7580'_114 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
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
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v2
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_app_104
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_fst_120
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_snd_124
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
-- Once.Spec.Core.Derived._.inᶜ
d_in'7580'_124 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_in'7580'_124 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_in'7580'_124 v4 v5
du_in'7580'_124 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_in'7580'_124 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
      (coe
         MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v0)
         (coe MAlonzo.Code.Once.Spec.Type.C_μ_28 (coe v0)))
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v1
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_roll_144 v0
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived._.outᶜ
d_out'7580'_128 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_out'7580'_128 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_out'7580'_128 v4 v5
du_out'7580'_128 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_out'7580'_128 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
      (coe
         MAlonzo.Code.Once.Spec.Type.C_ν_30 (coe v0)
         (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v1
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_out_156
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived._.composeᶜ
d_compose'7580'_140 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_compose'7580'_140 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_compose'7580'_140 v4 v5 v6 v7
du_compose'7580'_140 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_compose'7580'_140 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_108
      (coe MAlonzo.Code.Once.Spec.Grade.C_One_10) v2
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_108
         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
         (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_350 v3)
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100 v0
            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v1
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_app_104
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_app_104
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.Spec.Core.Derived._.pairᶜ
d_pair'7580'_152 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_pair'7580'_152 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_pair'7580'_152 v4 v5 v6 v7
du_pair'7580'_152 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_pair'7580'_152 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_108
      (coe MAlonzo.Code.Once.Spec.Grade.C_One_10) v2
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_108
         (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
         (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_350 v3)
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100 v0
            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v1
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_pair_116
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_app_104
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_app_104
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.Spec.Core.Derived._.caseᶜ
d_case'7580'_164 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_case'7580'_164 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_case'7580'_164 v4 v5 v6 v7 v8
du_case'7580'_164 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_case'7580'_164 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_108
      (coe MAlonzo.Code.Once.Spec.Grade.C_One_10) v3
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_108
         (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
         (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_350 v4)
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
            (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v0) (coe v1))
            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v2
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_case_136
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_app_104
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_app_104
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.Spec.Core.Derived._.curryᶜ
d_curry'7580'_178 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_curry'7580'_178 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_curry'7580'_178 v3 v4 v5 v6 v7
du_curry'7580'_178 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_curry'7580'_178 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_108
      (coe MAlonzo.Code.Once.Spec.Grade.C_One_10) v4
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100 v0
         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v2
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100 v1
            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v3
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_app_104
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_pair_116
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.Spec.Core.Derived._.cataᶜ
d_cata'7580'_192 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_cata'7580'_192 ~v0 ~v1 ~v2 v3 v4 v5 = du_cata'7580'_192 v3 v4 v5
du_cata'7580'_192 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_cata'7580'_192 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_108
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v2
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
         (coe MAlonzo.Code.Once.Spec.Type.C_μ_28 (coe v0))
         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v1
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_fold_148 v0
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
               (coe
                  MAlonzo.Code.Data.Fin.Base.C_suc_16
                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
-- Once.Spec.Core.Derived._.anaEffᶜ
d_anaEff'7580'_202 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_anaEff'7580'_202 ~v0 ~v1 ~v2 v3 v4 = du_anaEff'7580'_202 v3 v4
du_anaEff'7580'_202 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_anaEff'7580'_202 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_108
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v1
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100 v0
         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
         (coe MAlonzo.Code.Once.Spec.Grade.C_eff_44)
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_iter_160
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
               (coe
                  MAlonzo.Code.Data.Fin.Base.C_suc_16
                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
-- Once.Spec.Core.Derived._.anaᶜ
d_ana'7580'_210 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_ana'7580'_210 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_ana'7580'_210 v4 v5 v6 v7
du_ana'7580'_210 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_ana'7580'_210 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100 v1
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v2
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_unfold_152 v0
         (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_350 v3)
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.Spec.Core.Derived._.mapAtᶜ
d_mapAt'7580'_222 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_mapAt'7580'_222 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v6 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v9
        -> case coe v9 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Once.Spec.Core.Syntax.C_app_104 v7 v8
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v11 -> coe v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe v8
      MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe v8
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v9 v10
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_pair_116
             (d_mapAt'7580'_222
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v9)
                (coe v7) (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_fst_120 v8))
             (d_mapAt'7580'_222
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v10)
                (coe v7) (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_snd_124 v8))
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v9 v10
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_case_136
             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v8
             (coe
                MAlonzo.Code.Once.Spec.Core.Syntax.C_inl_128
                (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'_154
                   (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v2) (coe v10)
                   (coe MAlonzo.Code.Once.Spec.Type.du_at'8320'_224 (coe v5)))
                (d_mapAt'7580'_222
                   (coe v0) (coe v1) (coe v2)
                   (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4) (coe v5)
                   (coe v9) (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_350 v7)
                   (coe
                      MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
             (coe
                MAlonzo.Code.Once.Spec.Core.Syntax.C_inr_132
                (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'_154
                   (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v2) (coe v9)
                   (coe MAlonzo.Code.Once.Spec.Type.du_at'8320'_224 (coe v5)))
                (d_mapAt'7580'_222
                   (coe v0) (coe v1) (coe v2)
                   (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4) (coe v5)
                   (coe v10) (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_350 v7)
                   (coe
                      MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v9 v10 v11
        -> case coe v10 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v12 v13
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
                    (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'_154
                       (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v2) (coe v9)
                       (coe MAlonzo.Code.Once.Spec.Type.du_at'8320'_224 (coe v4)))
                    v12 v13
                    (coe
                       MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_108
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.Syntax.C_app_104
                          (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_350 v8)
                          (coe
                             MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                             (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                       (d_mapAt'7580'_222
                          (coe v0) (coe v1) (coe v2)
                          (coe addInt (coe (2 :: Integer)) (coe v3)) (coe v4) (coe v5)
                          (coe v11)
                          (coe
                             MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_350
                             (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_350 v7))
                          (coe
                             MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                             (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v9
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_fold_148
             (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'F_160
                (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v2) (coe v9)
                (coe MAlonzo.Code.Once.Spec.Type.du_at'8320'_224 (coe v4)))
             (coe
                MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
                (coe
                   MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50
                   (coe
                      MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'F_160
                      (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v2) (coe v9)
                      (coe MAlonzo.Code.Once.Spec.Type.du_at'8320'_224 (coe v4)))
                   (coe
                      MAlonzo.Code.Once.Spec.Type.C_μ_28
                      (coe
                         MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'F_160
                         (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v2) (coe v9)
                         (coe MAlonzo.Code.Once.Spec.Type.du_at'8320'_224 (coe v5)))))
                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                (coe
                   MAlonzo.Code.Once.Spec.Grade.C_fin_42
                   (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
                (coe
                   MAlonzo.Code.Once.Spec.Core.Syntax.C_roll_144
                   (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'F_160
                      (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v2) (coe v9)
                      (coe MAlonzo.Code.Once.Spec.Type.du_at'8320'_224 (coe v5)))
                   (d_mapLayer'7580'_226
                      (coe v0) (coe v1) (coe v2)
                      (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4) (coe v5)
                      (coe
                         MAlonzo.Code.Once.Spec.Type.C_μ_28
                         (coe
                            MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'F_160
                            (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v2) (coe v9)
                            (coe MAlonzo.Code.Once.Spec.Type.du_at'8320'_224 (coe v5))))
                      (coe v9) (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_350 v7)
                      (coe
                         MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
             v8
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v9 v10
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_unfold_152
             (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'F_160
                (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v2) (coe v9)
                (coe MAlonzo.Code.Once.Spec.Type.du_at'8320'_224 (coe v5)))
             (coe
                MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
                (coe
                   MAlonzo.Code.Once.Spec.Type.C_ν_30
                   (coe
                      MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'F_160
                      (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v2) (coe v9)
                      (coe MAlonzo.Code.Once.Spec.Type.du_at'8320'_224 (coe v4)))
                   (coe v10))
                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v10))
                (coe
                   MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_108
                   (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                   (coe
                      MAlonzo.Code.Once.Spec.Core.Syntax.C_out_156
                      (coe
                         MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                   (d_mapLayer'7580'_226
                      (coe v0) (coe v1) (coe v2)
                      (coe addInt (coe (2 :: Integer)) (coe v3)) (coe v4) (coe v5)
                      (coe
                         MAlonzo.Code.Once.Spec.Type.C_ν_30
                         (coe
                            MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'F_160
                            (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v2) (coe v9)
                            (coe MAlonzo.Code.Once.Spec.Type.du_at'8320'_224 (coe v4)))
                         (coe v10))
                      (coe v9)
                      (coe
                         MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_350
                         (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_350 v7))
                      (coe
                         MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
             v8
      MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe v8
      MAlonzo.Code.Once.Spec.Type.C_Float_34 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Derived._.mapLayerᶜ
d_mapLayer'7580'_226 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_mapLayer'7580'_226 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v7 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v10
        -> coe
             d_mapAt'7580'_222 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v10) (coe v8) (coe v9)
      MAlonzo.Code.Once.Spec.Type.C_Id_40 -> coe v9
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v10 v11
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_case_136
             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v9
             (coe
                MAlonzo.Code.Once.Spec.Core.Syntax.C_inl_128
                (coe
                   MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50
                   (coe
                      MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'F_160
                      (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v2) (coe v11)
                      (coe MAlonzo.Code.Once.Spec.Type.du_at'8320'_224 (coe v5)))
                   (coe v6))
                (d_mapLayer'7580'_226
                   (coe v0) (coe v1) (coe v2)
                   (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4) (coe v5)
                   (coe v6) (coe v10)
                   (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_350 v8)
                   (coe
                      MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
             (coe
                MAlonzo.Code.Once.Spec.Core.Syntax.C_inr_132
                (coe
                   MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50
                   (coe
                      MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'F_160
                      (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v2) (coe v10)
                      (coe MAlonzo.Code.Once.Spec.Type.du_at'8320'_224 (coe v5)))
                   (coe v6))
                (d_mapLayer'7580'_226
                   (coe v0) (coe v1) (coe v2)
                   (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4) (coe v5)
                   (coe v6) (coe v11)
                   (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_350 v8)
                   (coe
                      MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v10 v11
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_pair_116
             (d_mapLayer'7580'_226
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v10) (coe v8)
                (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_fst_120 v9))
             (d_mapLayer'7580'_226
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v11) (coe v8)
                (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_snd_124 v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Derived._.mapᶜ
d_map'7580'_392 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_map'7580'_392 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_108
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v7
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
         (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'_154
            (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v2) (coe v4)
            (coe MAlonzo.Code.Once.Spec.Type.du_at'8320'_224 (coe v5)))
         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
         (coe
            MAlonzo.Code.Once.Spec.Grade.C_fin_42
            (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
         (d_mapAt'7580'_222
            (coe v0) (coe v1) (coe v2)
            (coe addInt (coe (2 :: Integer)) (coe v3)) (coe v5) (coe v6)
            (coe v4)
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
               (coe
                  MAlonzo.Code.Data.Fin.Base.C_suc_16
                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
-- Once.Spec.Core.Derived._.layerᶜ
d_layer'7580'_404 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_layer'7580'_404 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      d_map'7580'_392 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50
         (coe
            MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'F_160 (coe v2)
            (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v4)
            (coe MAlonzo.Code.Once.Spec.Type.du_shift'7511'_234))
         (coe
            MAlonzo.Code.Once.Spec.Type.C_var_16
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
      (coe v5) (coe v6) (coe v7)
-- Once.Spec.Core.Derived._.effAppᶜ
d_effApp'7580'_416 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_effApp'7580'_416 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_effApp'7580'_416 v4 v5 v6
du_effApp'7580'_416 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_effApp'7580'_416 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
      (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v0
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_app_104
         (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_350 v1)
         (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_350 v2))
-- Once.Spec.Core.Derived._.applyEffᶜ
d_applyEff'7580'_426 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_applyEff'7580'_426 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_applyEff'7580'_426 v3 v4 v5 v6
du_applyEff'7580'_426 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_applyEff'7580'_426 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'42'__22
         (coe
            MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v1)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v0))
            (coe v2))
         (coe v1))
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v3
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v0
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_app_104
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_fst_120
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_snd_124
               (coe
                  MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.Spec.Core.Derived._.outActᶜ
d_outAct'7580'_438 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_outAct'7580'_438 ~v0 ~v1 ~v2 v3 v4 = du_outAct'7580'_438 v3 v4
du_outAct'7580'_438 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_outAct'7580'_438 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
      (coe
         MAlonzo.Code.Once.Spec.Type.C_ν_30 (coe v0)
         (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38))
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v1
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
         (coe
            MAlonzo.Code.Once.Spec.Grade.C_fin_42
            (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38))
         (coe
            MAlonzo.Code.Once.Spec.Core.Syntax.C_out_156
            (coe
               MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
               (coe
                  MAlonzo.Code.Data.Fin.Base.C_suc_16
                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
-- Once.Spec.Core.Derived._.appᵀ
d_app'7488'_446 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_app'7488'_446 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_app'7488'_446 v4 v5 v6
du_app'7488'_446 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_app'7488'_446 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v3
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe MAlonzo.Code.Once.Spec.Core.Syntax.C_app_104 v1 v2
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe du_effApp'7580'_416 (coe v0) (coe v1) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe du_effApp'7580'_416 (coe v0) (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Derived._.applyᵀ
d_apply'7488'_462 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_apply'7488'_462 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_apply'7488'_462 v4 v5 v6 v7
du_apply'7488'_462 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_apply'7488'_462 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v4
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
                    (coe
                       MAlonzo.Code.Once.Spec.Type.C__'42'__22
                       (coe
                          MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v0))
                          (coe v2))
                       (coe v1))
                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v3
                    (coe
                       MAlonzo.Code.Once.Spec.Core.Syntax.C_app_104
                       (coe
                          MAlonzo.Code.Once.Spec.Core.Syntax.C_fst_120
                          (coe
                             MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                             (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                       (coe
                          MAlonzo.Code.Once.Spec.Core.Syntax.C_snd_124
                          (coe
                             MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                             (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
                    (coe
                       MAlonzo.Code.Once.Spec.Type.C__'42'__22
                       (coe
                          MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v0))
                          (coe v2))
                       (coe v1))
                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v3
                    (coe
                       MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
                       (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v0
                       (coe
                          MAlonzo.Code.Once.Spec.Core.Syntax.C_app_104
                          (coe
                             MAlonzo.Code.Once.Spec.Core.Syntax.C_fst_120
                             (coe
                                MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                                (coe
                                   MAlonzo.Code.Data.Fin.Base.C_suc_16
                                   (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                          (coe
                             MAlonzo.Code.Once.Spec.Core.Syntax.C_snd_124
                             (coe
                                MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                                (coe
                                   MAlonzo.Code.Data.Fin.Base.C_suc_16
                                   (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
             (coe
                MAlonzo.Code.Once.Spec.Type.C__'42'__22
                (coe
                   MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v0))
                   (coe v2))
                (coe v1))
             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v3
             (coe
                MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
                (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v0
                (coe
                   MAlonzo.Code.Once.Spec.Core.Syntax.C_app_104
                   (coe
                      MAlonzo.Code.Once.Spec.Core.Syntax.C_fst_120
                      (coe
                         MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                         (coe
                            MAlonzo.Code.Data.Fin.Base.C_suc_16
                            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                   (coe
                      MAlonzo.Code.Once.Spec.Core.Syntax.C_snd_124
                      (coe
                         MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                         (coe
                            MAlonzo.Code.Data.Fin.Base.C_suc_16
                            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Derived._.outᵀ
d_out'7488'_484 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
d_out'7488'_484 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_out'7488'_484 v4 v5 v6
du_out'7488'_484 ::
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_86
du_out'7488'_484 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
        -> coe du_out'7580'_128 (coe v1) (coe v2)
      MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
        -> coe
             MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
             (coe MAlonzo.Code.Once.Spec.Type.C_ν_30 (coe v1) (coe v0))
             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v2
             (coe
                MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_100
                (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v0))
                (coe
                   MAlonzo.Code.Once.Spec.Core.Syntax.C_out_156
                   (coe
                      MAlonzo.Code.Once.Spec.Core.Syntax.C_var_96
                      (coe
                         MAlonzo.Code.Data.Fin.Base.C_suc_16
                         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
      _ -> MAlonzo.RTE.mazUnreachableError
