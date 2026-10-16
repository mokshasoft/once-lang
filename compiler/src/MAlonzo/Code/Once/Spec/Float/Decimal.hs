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

module MAlonzo.Code.Once.Spec.Float.Decimal where

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
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic

-- Once.Spec.Float.Decimal.Decimal
d_Decimal_8 = ()
data T_Decimal_8 = C__'47'10'94'__18 Integer Integer
-- Once.Spec.Float.Decimal.Decimal.sig
d_sig_14 :: T_Decimal_8 -> Integer
d_sig_14 v0
  = case coe v0 of
      C__'47'10'94'__18 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Decimal.Decimal.exp10
d_exp10_16 :: T_Decimal_8 -> Integer
d_exp10_16 v0
  = case coe v0 of
      C__'47'10'94'__18 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Decimal.fromℕ
d_fromℕ_20 :: Integer -> T_Decimal_8
d_fromℕ_20 v0 = coe C__'47'10'94'__18 (coe v0) (coe (0 :: Integer))
-- Once.Spec.Float.Decimal.negate
d_negate_24 :: T_Decimal_8 -> T_Decimal_8
d_negate_24 v0
  = case coe v0 of
      C__'47'10'94'__18 v1 v2
        -> coe
             C__'47'10'94'__18
             (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1)) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Decimal.decimalOf
d_decimalOf_30 :: Integer -> Integer -> Integer -> T_Decimal_8
d_decimalOf_30 v0 v1 v2
  = coe
      C__'47'10'94'__18
      (coe
         addInt
         (coe
            mulInt (coe v0)
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (10 :: Integer))
               (coe v2)))
         (coe v1))
      (coe v2)
-- Once.Spec.Float.Decimal.roundHalfEven
d_roundHalfEven_38 :: Integer -> Integer -> Integer -> Integer
d_roundHalfEven_38 v0 v1 v2
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
-- Once.Spec.Float.Decimal.divRHE
d_divRHE_48 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_divRHE_48 v0 v1 ~v2 = du_divRHE_48 v0 v1
du_divRHE_48 :: Integer -> Integer -> Integer
du_divRHE_48 v0 v1
  = coe
      d_roundHalfEven_38
      (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1))
      (coe MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v0) (coe v1))
      (coe v1)
-- Once.Spec.Float.Decimal.guardShift
d_guardShift_54 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer
d_guardShift_54 v0 v1
  = coe
      addInt
      (coe
         addInt (coe (4 :: Integer))
         (coe
            MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0)))
      (coe mulInt (coe (4 :: Integer)) (coe v1))
-- Once.Spec.Float.Decimal.binLen
d_binLen_60 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer
d_binLen_60 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Float.Dyadic.d_bitLen_66
      (coe
         MAlonzo.Code.Data.Nat.Base.du__'47'__318
         (coe
            mulInt (coe v1)
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
               (coe d_guardShift_54 (coe v0) (coe v2))))
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (10 :: Integer))
            (coe v2)))
-- Once.Spec.Float.Decimal.roundSig
d_roundSig_68 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_roundSig_68 v0 v1 v2
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             (coe (0 :: Integer))
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                du_go_84 (coe v3) (coe v2)
                (coe
                   MAlonzo.Code.Data.Integer.Base.d__'45'__302
                   (coe
                      addInt
                      (coe
                         addInt (coe (1 :: Integer))
                         (coe d_guardShift_54 (coe v0) (coe v2)))
                      (coe
                         MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0)))
                   (coe d_binLen_60 (coe v0) (coe v1) (coe v2))))
-- Once.Spec.Float.Decimal._.go
d_go_84 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_84 ~v0 v1 v2 v3 = du_go_84 v1 v2 v3
du_go_84 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_84 v0 v1 v2
  = case coe v2 of
      _ | coe geqInt (coe v2) (coe (0 :: Integer)) ->
          coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               du_divRHE_48
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
                du_divRHE_48 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe
                   mulInt
                   (coe
                      MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (10 :: Integer))
                      (coe v1))
                   (coe
                      MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                      (coe subInt (coe (0 :: Integer)) (coe v2)))))
             (coe subInt (coe (0 :: Integer)) (coe v2))
-- Once.Spec.Float.Decimal.storedExp
d_storedExp_90 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer
d_storedExp_90 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'43'__284
      (coe
         addInt (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_bias_50 (coe v0))
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
            (MAlonzo.Code.Once.Spec.Float.Dyadic.d_bitLen_66 (coe v1))
            (1 :: Integer)))
      (coe v2)
-- Once.Spec.Float.Decimal.maxFiniteExp
d_maxFiniteExp_98 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 -> Integer
d_maxFiniteExp_98 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
      (MAlonzo.Code.Data.Nat.Base.d__'94'__276
         (coe (2 :: Integer))
         (coe
            MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0)))
      (2 :: Integer)
-- Once.Spec.Float.Decimal.fracField
d_fracField_102 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer
d_fracField_102 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Float.Dyadic.d_modPow_54
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
      (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0))
-- Once.Spec.Float.Decimal.infinity
d_infinity_108 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer
d_infinity_108 v0 v1
  = coe
      addInt
      (coe
         mulInt
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
            (MAlonzo.Code.Data.Nat.Base.d__'94'__276
               (coe (2 :: Integer))
               (coe
                  MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0)))
            (1 :: Integer))
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe
               MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0))))
      (coe
         mulInt (coe v1)
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe
               addInt
               (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0))
               (coe
                  MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0)))))
-- Once.Spec.Float.Decimal.signedZero
d_signedZero_114 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer
d_signedZero_114 v0 v1
  = coe
      mulInt (coe v1)
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
         (coe
            addInt
            (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0))
            (coe
               MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0))))
-- Once.Spec.Float.Decimal.packHi
d_packHi_120 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer -> Bool -> Integer
d_packHi_120 v0 v1 v2 v3 v4
  = if coe v4
      then coe d_infinity_108 (coe v0) (coe v1)
      else coe
             addInt
             (coe
                addInt (coe d_fracField_102 (coe v0) (coe v2))
                (coe
                   mulInt
                   (coe
                      MAlonzo.Code.Once.Spec.Float.Dyadic.d_modPow_54 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0)))
                   (coe
                      MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                      (coe
                         MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0)))))
             (coe
                mulInt (coe v1)
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                   (coe
                      addInt
                      (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0))
                      (coe
                         MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0)))))
-- Once.Spec.Float.Decimal.packSE
d_packSE_138 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer -> Integer
d_packSE_138 v0 v1 v2 v3
  = case coe v3 of
      0 -> coe d_signedZero_114 (coe v0) (coe v1)
      _ | coe geqInt (coe v3) (coe (1 :: Integer)) ->
          coe
            d_packHi_120 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe ltInt (coe d_maxFiniteExp_98 (coe v0)) (coe v3))
      _ -> coe d_signedZero_114 (coe v0) (coe v1)
-- Once.Spec.Float.Decimal.packAt
d_packAt_160 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer -> Integer
d_packAt_160 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe d_signedZero_114 (coe v0) (coe v1)
      _ -> coe
             d_packSE_138 (coe v0) (coe v1) (coe v2)
             (coe d_storedExp_90 (coe v0) (coe v2) (coe v3))
-- Once.Spec.Float.Decimal.round
d_round_176 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  T_Decimal_8 -> Integer
d_round_176 v0 v1
  = coe
      d_packAt_160 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Float.Dyadic.d_signBit_70
         (coe d_sig_14 (coe v1)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_roundSig_68 (coe v0)
            (coe
               MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
               (coe d_sig_14 (coe v1)))
            (coe d_exp10_16 (coe v1))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            d_roundSig_68 (coe v0)
            (coe
               MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
               (coe d_sig_14 (coe v1)))
            (coe d_exp10_16 (coe v1))))
