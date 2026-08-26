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

module MAlonzo.Code.Once.Float.Decimal where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Float.Dyadic

-- Once.Float.Decimal.Decimal
d_Decimal_6 = ()
data T_Decimal_6 = C__'47'10'94'__16 Integer Integer
-- Once.Float.Decimal.Decimal.sig
d_sig_12 :: T_Decimal_6 -> Integer
d_sig_12 v0
  = case coe v0 of
      C__'47'10'94'__16 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Float.Decimal.Decimal.exp10
d_exp10_14 :: T_Decimal_6 -> Integer
d_exp10_14 v0
  = case coe v0 of
      C__'47'10'94'__16 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Float.Decimal.fromℕ
d_fromℕ_18 :: Integer -> T_Decimal_6
d_fromℕ_18 v0 = coe C__'47'10'94'__16 (coe v0) (coe (0 :: Integer))
-- Once.Float.Decimal.negate
d_negate_22 :: T_Decimal_6 -> T_Decimal_6
d_negate_22 v0
  = case coe v0 of
      C__'47'10'94'__16 v1 v2
        -> coe
             C__'47'10'94'__16
             (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1)) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Float.Decimal.decimalOf
d_decimalOf_28 :: Integer -> Integer -> Integer -> T_Decimal_6
d_decimalOf_28 v0 v1 v2
  = coe
      C__'47'10'94'__16
      (coe
         addInt
         (coe
            mulInt (coe v0)
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (10 :: Integer))
               (coe v2)))
         (coe v1))
      (coe v2)
-- Once.Float.Decimal.roundHalfEven
d_roundHalfEven_36 :: Integer -> Integer -> Integer -> Integer
d_roundHalfEven_36 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe ltInt (coe mulInt (coe (2 :: Integer)) (coe v1)) (coe v2))
      (coe v0)
      (coe
         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
         (coe ltInt (coe v2) (coe mulInt (coe (2 :: Integer)) (coe v1)))
         (coe addInt (coe (1 :: Integer)) (coe v0))
         (coe
            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
            (coe
               eqInt
               (coe
                  MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v0)
                  (coe (2 :: Integer)))
               (coe (0 :: Integer)))
            (coe v0) (coe addInt (coe (1 :: Integer)) (coe v0))))
-- Once.Float.Decimal.divRHE
d_divRHE_46 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_divRHE_46 v0 v1 ~v2 = du_divRHE_46 v0 v1
du_divRHE_46 :: Integer -> Integer -> Integer
du_divRHE_46 v0 v1
  = coe
      d_roundHalfEven_36
      (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1))
      (coe MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v0) (coe v1))
      (coe v1)
-- Once.Float.Decimal.guardShift
d_guardShift_52 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer
d_guardShift_52 v0 v1
  = coe
      addInt
      (coe
         addInt (coe (4 :: Integer))
         (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0)))
      (coe mulInt (coe (4 :: Integer)) (coe v1))
-- Once.Float.Decimal.binLen
d_binLen_58 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer -> Integer
d_binLen_58 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Float.Dyadic.d_bitLen_110
      (coe
         MAlonzo.Code.Data.Nat.Base.du__'47'__318
         (coe
            mulInt (coe v1)
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
               (coe d_guardShift_52 (coe v0) (coe v2))))
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (10 :: Integer))
            (coe v2)))
-- Once.Float.Decimal.roundSig
d_roundSig_66 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_roundSig_66 v0 v1 v2
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             (coe (0 :: Integer))
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                du_go_82 (coe v3) (coe v2)
                (coe
                   MAlonzo.Code.Data.Integer.Base.d__'45'__302
                   (coe
                      addInt
                      (coe
                         addInt (coe (1 :: Integer))
                         (coe d_guardShift_52 (coe v0) (coe v2)))
                      (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0)))
                   (coe d_binLen_58 (coe v0) (coe v1) (coe v2))))
-- Once.Float.Decimal._.go
d_go_82 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_82 ~v0 v1 v2 v3 = du_go_82 v1 v2 v3
du_go_82 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_82 v0 v1 v2
  = case coe v2 of
      _ | coe geqInt (coe v2) (coe (0 :: Integer)) ->
          coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               du_divRHE_46
               (coe
                  mulInt (coe addInt (coe (1 :: Integer)) (coe v0))
                  (coe
                     MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                     (coe v2)))
               (coe
                  MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (10 :: Integer))
                  (coe v1)))
            (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2))
      _ -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_divRHE_46 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe
                   mulInt
                   (coe
                      MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (10 :: Integer))
                      (coe v1))
                   (coe
                      MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                      (coe subInt (coe (0 :: Integer)) (coe v2)))))
             (coe subInt (coe (0 :: Integer)) (coe v2))
-- Once.Float.Decimal.storedExp
d_storedExp_88 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer -> Integer
d_storedExp_88 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'43'__284
      (coe
         addInt (coe MAlonzo.Code.Once.Float.Dyadic.d_bias_48 (coe v0))
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
            (MAlonzo.Code.Once.Float.Dyadic.d_bitLen_110 (coe v1))
            (1 :: Integer)))
      (coe v2)
-- Once.Float.Decimal.maxFiniteExp
d_maxFiniteExp_96 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 -> Integer
d_maxFiniteExp_96 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
      (MAlonzo.Code.Data.Nat.Base.d__'94'__276
         (coe (2 :: Integer))
         (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0)))
      (2 :: Integer)
-- Once.Float.Decimal.fracField
d_fracField_100 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer
d_fracField_100 v0 v1
  = coe
      MAlonzo.Code.Once.Float.Dyadic.d_modPow_52
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
                     (MAlonzo.Code.Once.Float.Dyadic.d_bitLen_110 (coe v1))
                     (1 :: Integer))))
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
               (coe
                  MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                  (MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                     (MAlonzo.Code.Once.Float.Dyadic.d_bitLen_110 (coe v1))
                     (1 :: Integer)))))
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe
               MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
               (coe
                  MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                  (MAlonzo.Code.Once.Float.Dyadic.d_bitLen_110 (coe v1))
                  (1 :: Integer))
               (MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0)))))
      (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0))
-- Once.Float.Decimal.infinity
d_infinity_106 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer
d_infinity_106 v0 v1
  = coe
      addInt
      (coe
         mulInt
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
            (MAlonzo.Code.Data.Nat.Base.d__'94'__276
               (coe (2 :: Integer))
               (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0)))
            (1 :: Integer))
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0))))
      (coe
         mulInt (coe v1)
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe
               addInt
               (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0))
               (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0)))))
-- Once.Float.Decimal.signedZero
d_signedZero_112 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer
d_signedZero_112 v0 v1
  = coe
      mulInt (coe v1)
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
         (coe
            addInt
            (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0))
            (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0))))
-- Once.Float.Decimal.packHi
d_packHi_118 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer -> Integer -> Bool -> Integer
d_packHi_118 v0 v1 v2 v3 v4
  = if coe v4
      then coe d_infinity_106 (coe v0) (coe v1)
      else coe
             addInt
             (coe
                addInt (coe d_fracField_100 (coe v0) (coe v2))
                (coe
                   mulInt
                   (coe
                      MAlonzo.Code.Once.Float.Dyadic.d_modPow_52 (coe v3)
                      (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0)))
                   (coe
                      MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                      (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0)))))
             (coe
                mulInt (coe v1)
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                   (coe
                      addInt
                      (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0))
                      (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0)))))
-- Once.Float.Decimal.packSE
d_packSE_136 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer -> Integer -> Integer
d_packSE_136 v0 v1 v2 v3
  = case coe v3 of
      0 -> coe d_signedZero_112 (coe v0) (coe v1)
      _ | coe geqInt (coe v3) (coe (1 :: Integer)) ->
          coe
            d_packHi_118 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe ltInt (coe d_maxFiniteExp_96 (coe v0)) (coe v3))
      _ -> coe d_signedZero_112 (coe v0) (coe v1)
-- Once.Float.Decimal.packAt
d_packAt_158 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer -> Integer -> Integer
d_packAt_158 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe d_signedZero_112 (coe v0) (coe v1)
      _ -> coe
             d_packSE_136 (coe v0) (coe v1) (coe v2)
             (coe d_storedExp_88 (coe v0) (coe v2) (coe v3))
-- Once.Float.Decimal.round
d_round_174 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  T_Decimal_6 -> Integer
d_round_174 v0 v1
  = coe
      d_packAt_158 (coe v0)
      (coe
         MAlonzo.Code.Once.Float.Dyadic.d_signBit_114
         (coe d_sig_12 (coe v1)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_roundSig_66 (coe v0)
            (coe
               MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
               (coe d_sig_12 (coe v1)))
            (coe d_exp10_14 (coe v1))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            d_roundSig_66 (coe v0)
            (coe
               MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
               (coe d_sig_12 (coe v1)))
            (coe d_exp10_14 (coe v1))))
-- Once.Float.Decimal.magInf
d_magInf_182 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_magInf_182 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'737''45''60'_4240
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
         (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0)))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (MAlonzo.Code.Data.Nat.Base.d__'94'__276
            (coe (2 :: Integer))
            (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0)))
         (1 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (MAlonzo.Code.Data.Nat.Base.d__'94'__276
            (coe (2 :: Integer))
            (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0)))
         (0 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'691''45''60'_5276
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0)))
         (coe (1 :: Integer)) (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
         (coe MAlonzo.Code.Data.Nat.Properties.du_m'94'n'62'0_4482))
-- Once.Float.Decimal.magFin
d_magFin_194 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_magFin_194 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Float.Dyadic.du_combine'45'bound_76
      (coe
         MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v2)
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0))))
      (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0))
      (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0))
      (coe
         MAlonzo.Code.Once.Float.Dyadic.d_modPow'60'_62 (coe v2)
         (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0)))
      (coe
         MAlonzo.Code.Once.Float.Dyadic.d_modPow'60'_62
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
                        (MAlonzo.Code.Once.Float.Dyadic.d_bitLen_110 (coe v1))
                        (1 :: Integer))))
               (coe
                  MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                     (MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                        (MAlonzo.Code.Once.Float.Dyadic.d_bitLen_110 (coe v1))
                        (1 :: Integer)))))
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
               (coe
                  MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                  (coe
                     MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                     (MAlonzo.Code.Once.Float.Dyadic.d_bitLen_110 (coe v1))
                     (1 :: Integer))
                  (MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0)))))
         (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0)))
-- Once.Float.Decimal.packHi-fits
d_packHi'45'fits_212 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  Integer ->
  Integer ->
  Bool ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_packHi'45'fits_212 v0 v1 v2 v3 v4 v5
  = if coe v4
      then coe
             MAlonzo.Code.Once.Float.Dyadic.du_combine'45'bound_76 (coe v1)
             (coe (1 :: Integer))
             (coe
                addInt
                (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0))
                (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0)))
             (coe v5) (coe d_magInf_182 (coe v0))
      else coe
             MAlonzo.Code.Once.Float.Dyadic.du_combine'45'bound_76 (coe v1)
             (coe (1 :: Integer))
             (coe
                addInt
                (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0))
                (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0)))
             (coe v5) (coe d_magFin_194 (coe v0) (coe v2) (coe v3))
-- Once.Float.Decimal.packSE-fits
d_packSE'45'fits_242 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_packSE'45'fits_242 v0 v1 v2 v3 v4
  = case coe v3 of
      0 -> coe
             MAlonzo.Code.Once.Float.Dyadic.du_combine'45'bound_76 (coe v1)
             (coe (1 :: Integer))
             (coe
                addInt
                (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0))
                (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0)))
             (coe v4) (coe MAlonzo.Code.Data.Nat.Properties.du_m'94'n'62'0_4482)
      _ | coe geqInt (coe v3) (coe (1 :: Integer)) ->
          coe
            d_packHi'45'fits_212 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe ltInt (coe d_maxFiniteExp_96 (coe v0)) (coe v3)) (coe v4)
      _ -> coe
             MAlonzo.Code.Once.Float.Dyadic.du_combine'45'bound_76 (coe v1)
             (coe (1 :: Integer))
             (coe
                addInt
                (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0))
                (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0)))
             (coe v4) (coe MAlonzo.Code.Data.Nat.Properties.du_m'94'n'62'0_4482)
-- Once.Float.Decimal.packAt-fits
d_packAt'45'fits_278 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_packAt'45'fits_278 v0 v1 v2 v3 v4
  = case coe v2 of
      0 -> coe
             MAlonzo.Code.Once.Float.Dyadic.du_combine'45'bound_76 (coe v1)
             (coe (1 :: Integer))
             (coe
                addInt
                (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0))
                (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0)))
             (coe v4) (coe MAlonzo.Code.Data.Nat.Properties.du_m'94'n'62'0_4482)
      _ -> coe
             d_packSE'45'fits_242 (coe v0) (coe v1) (coe v2)
             (coe d_storedExp_88 (coe v0) (coe v2) (coe v3)) (coe v4)
-- Once.Float.Decimal.round-fits
d_round'45'fits_302 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  T_Decimal_6 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_round'45'fits_302 v0 v1
  = coe
      d_packAt'45'fits_278 (coe v0)
      (coe
         MAlonzo.Code.Once.Float.Dyadic.d_signBit_114
         (coe d_sig_12 (coe v1)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_roundSig_66 (coe v0)
            (coe
               MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
               (coe d_sig_12 (coe v1)))
            (coe d_exp10_14 (coe v1))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            d_roundSig_66 (coe v0)
            (coe
               MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
               (coe d_sig_12 (coe v1)))
            (coe d_exp10_14 (coe v1))))
      (coe
         MAlonzo.Code.Once.Float.Dyadic.d_signBit'60'_166
         (coe d_sig_12 (coe v1)))
