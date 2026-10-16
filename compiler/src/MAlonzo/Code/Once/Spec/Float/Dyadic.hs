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

module MAlonzo.Code.Once.Spec.Float.Dyadic where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base

-- Once.Spec.Float.Dyadic.Dyadic
d_Dyadic_8 = ()
data T_Dyadic_8 = C__'47'2'94'__18 Integer Integer
-- Once.Spec.Float.Dyadic.Dyadic.sig
d_sig_14 :: T_Dyadic_8 -> Integer
d_sig_14 v0
  = case coe v0 of
      C__'47'2'94'__18 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Dyadic.Dyadic.shift
d_shift_16 :: T_Dyadic_8 -> Integer
d_shift_16 v0
  = case coe v0 of
      C__'47'2'94'__18 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Dyadic.fromℕ
d_fromℕ_20 :: Integer -> T_Dyadic_8
d_fromℕ_20 v0 = coe C__'47'2'94'__18 (coe v0) (coe (0 :: Integer))
-- Once.Spec.Float.Dyadic.negate
d_negate_24 :: T_Dyadic_8 -> T_Dyadic_8
d_negate_24 v0
  = case coe v0 of
      C__'47'2'94'__18 v1 v2
        -> coe
             C__'47'2'94'__18
             (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1)) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Dyadic.FloatFormat
d_FloatFormat_30 = ()
data T_FloatFormat_30 = C_mkFormat_40 Integer Integer
-- Once.Spec.Float.Dyadic.FloatFormat.sig-bits
d_sig'45'bits_36 :: T_FloatFormat_30 -> Integer
d_sig'45'bits_36 v0
  = case coe v0 of
      C_mkFormat_40 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Dyadic.FloatFormat.exp-bits
d_exp'45'bits_38 :: T_FloatFormat_30 -> Integer
d_exp'45'bits_38 v0
  = case coe v0 of
      C_mkFormat_40 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Dyadic.binary32
d_binary32_42 :: T_FloatFormat_30
d_binary32_42
  = coe C_mkFormat_40 (coe (23 :: Integer)) (coe (8 :: Integer))
-- Once.Spec.Float.Dyadic.binary64
d_binary64_44 :: T_FloatFormat_30
d_binary64_44
  = coe C_mkFormat_40 (coe (52 :: Integer)) (coe (11 :: Integer))
-- Once.Spec.Float.Dyadic.width
d_width_46 :: T_FloatFormat_30 -> Integer
d_width_46 v0
  = coe
      addInt
      (coe addInt (coe (1 :: Integer)) (coe d_exp'45'bits_38 (coe v0)))
      (coe d_sig'45'bits_36 (coe v0))
-- Once.Spec.Float.Dyadic.bias
d_bias_50 :: T_FloatFormat_30 -> Integer
d_bias_50 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
      (MAlonzo.Code.Data.Nat.Base.d__'94'__276
         (coe (2 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
            (d_exp'45'bits_38 (coe v0)) (1 :: Integer)))
      (1 :: Integer)
-- Once.Spec.Float.Dyadic.modPow
d_modPow_54 :: Integer -> Integer -> Integer
d_modPow_54 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
         (coe v1))
-- Once.Spec.Float.Dyadic.bitLen-go
d_bitLen'45'go_60 :: Integer -> Integer -> Integer
d_bitLen'45'go_60 v0 v1
  = case coe v0 of
      0 -> coe (0 :: Integer)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe (0 :: Integer)
                _ -> coe
                       addInt (coe (1 :: Integer))
                       (coe
                          d_bitLen'45'go_60 (coe v2)
                          (coe
                             MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v1)
                             (coe (2 :: Integer)))))
-- Once.Spec.Float.Dyadic.bitLen
d_bitLen_66 :: Integer -> Integer
d_bitLen_66 v0 = coe d_bitLen'45'go_60 (coe v0) (coe v0)
-- Once.Spec.Float.Dyadic.signBit
d_signBit_70 :: Integer -> Integer
d_signBit_70 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) -> coe (0 :: Integer)
      _ -> coe (1 :: Integer)
-- Once.Spec.Float.Dyadic.expFieldN
d_expFieldN_72 :: T_FloatFormat_30 -> Integer -> Integer -> Integer
d_expFieldN_72 v0 v1 v2
  = coe
      d_modPow_54
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (addInt
            (coe d_bias_50 (coe v0))
            (coe
               MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_bitLen_66 (coe v1))
               (1 :: Integer)))
         v2)
      (coe d_exp'45'bits_38 (coe v0))
-- Once.Spec.Float.Dyadic.sigFieldN
d_sigFieldN_80 :: T_FloatFormat_30 -> Integer -> Integer -> Integer
d_sigFieldN_80 v0 v1 ~v2 = du_sigFieldN_80 v0 v1
du_sigFieldN_80 :: T_FloatFormat_30 -> Integer -> Integer
du_sigFieldN_80 v0 v1
  = coe
      d_modPow_54
      (coe
         mulInt
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1
            (MAlonzo.Code.Data.Nat.Base.d__'94'__276
               (coe (2 :: Integer))
               (coe
                  MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_bitLen_66 (coe v1))
                  (1 :: Integer))))
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe
               MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
               (d_sig'45'bits_36 (coe v0))
               (coe
                  MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_bitLen_66 (coe v1))
                  (1 :: Integer)))))
      (coe d_sig'45'bits_36 (coe v0))
-- Once.Spec.Float.Dyadic.encodeMag
d_encodeMag_86 :: T_FloatFormat_30 -> Integer -> Integer -> Integer
d_encodeMag_86 v0 v1 v2
  = case coe v1 of
      0 -> coe (0 :: Integer)
      _ -> coe
             addInt (coe du_sigFieldN_80 (coe v0) (coe v1))
             (coe
                mulInt (coe d_expFieldN_72 (coe v0) (coe v1) (coe v2))
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                   (coe d_sig'45'bits_36 (coe v0))))
-- Once.Spec.Float.Dyadic.encode
d_encode_96 :: T_FloatFormat_30 -> T_Dyadic_8 -> Integer
d_encode_96 v0 v1
  = coe
      addInt
      (coe
         d_encodeMag_86 (coe v0)
         (coe
            MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
            (coe d_sig_14 (coe v1)))
         (coe d_shift_16 (coe v1)))
      (coe
         mulInt (coe d_signBit_70 (coe d_sig_14 (coe v1)))
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe
               addInt (coe d_exp'45'bits_38 (coe v0))
               (coe d_sig'45'bits_36 (coe v0)))))
