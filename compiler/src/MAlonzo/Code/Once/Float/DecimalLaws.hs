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

module MAlonzo.Code.Once.Float.DecimalLaws where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Float.DyadicLaws
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic

-- Once.Float.DecimalLaws.magInf
d_magInf_8 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_magInf_8 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'737''45''60'_4240
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
         (coe
            MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0)))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (MAlonzo.Code.Data.Nat.Base.d__'94'__276
            (coe (2 :: Integer))
            (coe
               MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0)))
         (1 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (MAlonzo.Code.Data.Nat.Base.d__'94'__276
            (coe (2 :: Integer))
            (coe
               MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0)))
         (0 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'691''45''60'_5276
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe
               MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0)))
         (coe (1 :: Integer)) (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
         (coe MAlonzo.Code.Data.Nat.Properties.du_m'94'n'62'0_4482))
-- Once.Float.DecimalLaws.magFin
d_magFin_20 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_magFin_20 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Float.DyadicLaws.du_combine'45'bound_24
      (coe
         MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v2)
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe
               MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0))))
      (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0))
      (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0))
      (coe
         MAlonzo.Code.Once.Float.DyadicLaws.d_modPow'60'_10 (coe v2)
         (coe
            MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0)))
      (coe
         MAlonzo.Code.Once.Float.DyadicLaws.d_modPow'60'_10
         (coe
            MAlonzo.Code.Data.Nat.Base.du__'47'__318
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
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
               (coe
                  MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                  (coe
                     MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                     (MAlonzo.Code.Once.Spec.Float.Dyadic.d_bitLen_66 (coe v1))
                     (1 :: Integer))
                  (MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0)))))
         (coe
            MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0)))
-- Once.Float.DecimalLaws.packHi-fits
d_packHi'45'fits_38 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer ->
  Integer ->
  Integer ->
  Bool ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_packHi'45'fits_38 v0 v1 v2 v3 v4 v5
  = if coe v4
      then coe
             MAlonzo.Code.Once.Float.DyadicLaws.du_combine'45'bound_24 (coe v1)
             (coe (1 :: Integer))
             (coe
                addInt
                (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0))
                (coe
                   MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0)))
             (coe v5) (coe d_magInf_8 (coe v0))
      else coe
             MAlonzo.Code.Once.Float.DyadicLaws.du_combine'45'bound_24 (coe v1)
             (coe (1 :: Integer))
             (coe
                addInt
                (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0))
                (coe
                   MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0)))
             (coe v5) (coe d_magFin_20 (coe v0) (coe v2) (coe v3))
-- Once.Float.DecimalLaws.packSE-fits
d_packSE'45'fits_68 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_packSE'45'fits_68 v0 v1 v2 v3 v4
  = case coe v3 of
      0 -> coe
             MAlonzo.Code.Once.Float.DyadicLaws.du_combine'45'bound_24 (coe v1)
             (coe (1 :: Integer))
             (coe
                addInt
                (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0))
                (coe
                   MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0)))
             (coe v4) (coe MAlonzo.Code.Data.Nat.Properties.du_m'94'n'62'0_4482)
      _ | coe geqInt (coe v3) (coe (1 :: Integer)) ->
          coe
            d_packHi'45'fits_38 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe
               ltInt
               (coe
                  MAlonzo.Code.Once.Spec.Float.Decimal.d_maxFiniteExp_98 (coe v0))
               (coe v3))
            (coe v4)
      _ -> coe
             MAlonzo.Code.Once.Float.DyadicLaws.du_combine'45'bound_24 (coe v1)
             (coe (1 :: Integer))
             (coe
                addInt
                (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0))
                (coe
                   MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0)))
             (coe v4) (coe MAlonzo.Code.Data.Nat.Properties.du_m'94'n'62'0_4482)
-- Once.Float.DecimalLaws.packAt-fits
d_packAt'45'fits_104 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_packAt'45'fits_104 v0 v1 v2 v3 v4
  = case coe v2 of
      0 -> coe
             MAlonzo.Code.Once.Float.DyadicLaws.du_combine'45'bound_24 (coe v1)
             (coe (1 :: Integer))
             (coe
                addInt
                (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0))
                (coe
                   MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0)))
             (coe v4) (coe MAlonzo.Code.Data.Nat.Properties.du_m'94'n'62'0_4482)
      _ -> coe
             d_packSE'45'fits_68 (coe v0) (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.Spec.Float.Decimal.d_storedExp_90 (coe v0)
                (coe v2) (coe v3))
             (coe v4)
-- Once.Float.DecimalLaws.round-fits
d_round'45'fits_128 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Spec.Float.Decimal.T_Decimal_8 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_round'45'fits_128 v0 v1
  = coe
      d_packAt'45'fits_104 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Float.Dyadic.d_signBit_70
         (coe MAlonzo.Code.Once.Spec.Float.Decimal.d_sig_14 (coe v1)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.Spec.Float.Decimal.d_roundSig_68 (coe v0)
            (coe
               MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
               (coe MAlonzo.Code.Once.Spec.Float.Decimal.d_sig_14 (coe v1)))
            (coe MAlonzo.Code.Once.Spec.Float.Decimal.d_exp10_16 (coe v1))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.Spec.Float.Decimal.d_roundSig_68 (coe v0)
            (coe
               MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
               (coe MAlonzo.Code.Once.Spec.Float.Decimal.d_sig_14 (coe v1)))
            (coe MAlonzo.Code.Once.Spec.Float.Decimal.d_exp10_16 (coe v1))))
      (coe
         MAlonzo.Code.Once.Float.DyadicLaws.d_signBit'60'_72
         (coe MAlonzo.Code.Once.Spec.Float.Decimal.d_sig_14 (coe v1)))
