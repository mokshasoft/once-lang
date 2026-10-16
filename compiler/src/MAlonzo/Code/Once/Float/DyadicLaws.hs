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

module MAlonzo.Code.Once.Float.DyadicLaws where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.DivMod
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic

-- Once.Float.DyadicLaws.modPow<
d_modPow'60'_10 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_modPow'60'_10 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.DivMod.du_m'37'n'60'n_166 (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
         (coe v1))
-- Once.Float.DyadicLaws.combine-bound
d_combine'45'bound_24 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_combine'45'bound_24 v0 ~v1 v2 v3 v4 v5
  = du_combine'45'bound_24 v0 v2 v3 v4 v5
du_combine'45'bound_24 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_combine'45'bound_24 v0 v1 v2 v3 v4
  = coe du_lemma_50 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.Float.DyadicLaws._.step1
d_step1_42 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_step1_42 v0 ~v1 ~v2 v3 ~v4 v5 = du_step1_42 v0 v3 v5
du_step1_42 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_step1_42 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3714
      (coe
         mulInt (coe v0)
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe v1)))
      (coe v2)
-- Once.Float.DyadicLaws._.step2
d_step2_44 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step2_44 = erased
-- Once.Float.DyadicLaws._.step3
d_step3_46 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_step3_46 v0 ~v1 v2 v3 v4 ~v5 = du_step3_46 v0 v2 v3 v4
du_step3_46 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_step3_46 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'737''45''8804'_4222
      (MAlonzo.Code.Data.Nat.Base.d__'94'__276
         (coe (2 :: Integer)) (coe v2))
      (addInt (coe (1 :: Integer)) (coe v0))
      (MAlonzo.Code.Data.Nat.Base.d__'94'__276
         (coe (2 :: Integer)) (coe v1))
      v3
-- Once.Float.DyadicLaws._.step4
d_step4_48 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step4_48 = erased
-- Once.Float.DyadicLaws._.lemma
d_lemma_50 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lemma_50 v0 ~v1 v2 v3 v4 v5 = du_lemma_50 v0 v2 v3 v4 v5
du_lemma_50 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lemma_50 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
      (coe du_step1_42 (coe v0) (coe v2) (coe v4))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
            (coe
               addInt
               (coe
                  MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                  (coe v2))
               (coe
                  mulInt (coe v0)
                  (coe
                     MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                     (coe v2)))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
            (coe du_step3_46 (coe v0) (coe v1) (coe v2) (coe v3))
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
               (coe
                  mulInt
                  (coe
                     MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                     (coe v1))
                  (coe
                     MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                     (coe v2))))))
-- Once.Float.DyadicLaws.encodeMag-fits
d_encodeMag'45'fits_58 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_encodeMag'45'fits_58 v0 v1 v2
  = case coe v1 of
      0 -> coe MAlonzo.Code.Data.Nat.Properties.du_m'94'n'62'0_4482
      _ -> coe
             du_combine'45'bound_24
             (coe
                MAlonzo.Code.Data.Nat.Base.du__'37'__330
                (coe
                   MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                   (addInt
                      (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_bias_50 (coe v0))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                         (MAlonzo.Code.Once.Spec.Float.Dyadic.d_bitLen_66 (coe v1))
                         (1 :: Integer)))
                   v2)
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                   (coe
                      MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0))))
             (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0))
             (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0))
             (coe
                d_modPow'60'_10
                (coe
                   MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                   (addInt
                      (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_bias_50 (coe v0))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                         (MAlonzo.Code.Once.Spec.Float.Dyadic.d_bitLen_66 (coe v1))
                         (1 :: Integer)))
                   v2)
                (coe
                   MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0)))
             (coe
                d_modPow'60'_10
                (coe
                   mulInt
                   (coe
                      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1
                      (MAlonzo.Code.Data.Nat.Base.d__'94'__276
                         (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                            (MAlonzo.Code.Once.Spec.Float.Dyadic.d_bitLen_66 (coe v1))
                            (1 :: Integer))))
                   (coe
                      MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                         (MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                            (MAlonzo.Code.Once.Spec.Float.Dyadic.d_bitLen_66 (coe v1))
                            (1 :: Integer)))))
                (coe
                   MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0)))
-- Once.Float.DyadicLaws.signBit<
d_signBit'60'_72 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_signBit'60'_72 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      _ -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- Once.Float.DyadicLaws.encode-fits
d_encode'45'fits_78 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_Dyadic_8 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_encode'45'fits_78 v0 v1
  = coe
      du_combine'45'bound_24
      (coe
         MAlonzo.Code.Once.Spec.Float.Dyadic.d_signBit_70
         (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig_14 (coe v1)))
      (coe (1 :: Integer))
      (coe
         addInt
         (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0))
         (coe
            MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0)))
      (coe
         d_signBit'60'_72
         (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig_14 (coe v1)))
      (coe
         d_encodeMag'45'fits_58 (coe v0)
         (coe
            MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
            (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig_14 (coe v1)))
         (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_shift_16 (coe v1)))
