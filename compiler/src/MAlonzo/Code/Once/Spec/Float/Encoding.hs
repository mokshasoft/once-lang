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

module MAlonzo.Code.Once.Spec.Float.Encoding where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic
import qualified MAlonzo.Code.Once.Spec.Float.Value

-- Once.Spec.Float.Encoding.signBitOf
d_signBitOf_8 ::
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 -> Integer
d_signBitOf_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Float.Value.C_pos_10 -> coe (0 :: Integer)
      MAlonzo.Code.Once.Spec.Float.Value.C_neg_12 -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Encoding.signWeight
d_signWeight_10 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 -> Integer
d_signWeight_10 v0
  = coe
      MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
      (coe
         addInt
         (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_42 (coe v0))
         (coe
            MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_40 (coe v0)))
-- Once.Spec.Float.Encoding.maxExpField
d_maxExpField_14 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 -> Integer
d_maxExpField_14 v0
  = coe
      mulInt
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (MAlonzo.Code.Data.Nat.Base.d__'94'__276
            (coe (2 :: Integer))
            (coe
               MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_42 (coe v0)))
         (1 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
         (coe
            MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_40 (coe v0)))
-- Once.Spec.Float.Encoding.zeroW
d_zeroW_18 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 -> Integer
d_zeroW_18 v0 v1
  = coe
      mulInt (coe d_signBitOf_8 (coe v1)) (coe d_signWeight_10 (coe v0))
-- Once.Spec.Float.Encoding.infW
d_infW_24 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 -> Integer
d_infW_24 v0 v1
  = coe
      addInt (coe d_maxExpField_14 (coe v0))
      (coe
         mulInt (coe d_signBitOf_8 (coe v1)) (coe d_signWeight_10 (coe v0)))
-- Once.Spec.Float.Encoding.nanW
d_nanW_30 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 -> Integer
d_nanW_30 v0
  = coe
      addInt
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
            (MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_40 (coe v0))
            (1 :: Integer)))
      (coe d_maxExpField_14 (coe v0))
-- Once.Spec.Float.Encoding.normalW
d_normalW_34 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer -> Integer -> Integer
d_normalW_34 v0 v1 v2 v3
  = coe
      addInt
      (coe
         addInt
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
            (mulInt
               (coe v2)
               (coe
                  MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                     (addInt
                        (coe (1 :: Integer))
                        (coe
                           MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_40 (coe v0)))
                     (MAlonzo.Code.Once.Spec.Float.Dyadic.d_bitLen_74 (coe v2)))))
            (MAlonzo.Code.Data.Nat.Base.d__'94'__276
               (coe (2 :: Integer))
               (coe
                  MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_40 (coe v0))))
         (coe
            mulInt (coe d_signBitOf_8 (coe v1))
            (coe d_signWeight_10 (coe v0))))
      (coe
         mulInt (coe v3)
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe
               MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_40 (coe v0))))
-- Once.Spec.Float.Encoding.subnormalW
d_subnormalW_44 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer -> Integer -> Integer
d_subnormalW_44 v0 v1 v2 v3
  = case coe v3 of
      _ | coe geqInt (coe v3) (coe (0 :: Integer)) ->
          coe
            addInt
            (coe
               mulInt (coe d_signBitOf_8 (coe v1)) (coe d_signWeight_10 (coe v0)))
            (coe
               mulInt (coe v2)
               (coe
                  MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                  (coe v3)))
      _ -> coe
             mulInt (coe d_signBitOf_8 (coe v1)) (coe d_signWeight_10 (coe v0))
-- Once.Spec.Float.Encoding.numAt
d_numAt_60 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer -> Integer -> Integer -> Integer
d_numAt_60 v0 v1 v2 v3 v4
  = case coe v4 of
      0 -> coe
             d_subnormalW_44 (coe v0) (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v3)
                (coe MAlonzo.Code.Once.Spec.Float.Value.d_qmin_66 (coe v0)))
      _ | coe geqInt (coe v4) (coe (1 :: Integer)) ->
          coe d_normalW_34 (coe v0) (coe v1) (coe v2) (coe v4)
      _ -> coe
             d_subnormalW_44 (coe v0) (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v3)
                (coe MAlonzo.Code.Once.Spec.Float.Value.d_qmin_66 (coe v0)))
-- Once.Spec.Float.Encoding.encode
d_encode_88 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 -> Integer
d_encode_88 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'zero_26 v2
        -> coe d_zeroW_18 (coe v0) (coe v2)
      MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'num_28 v2 v3 v4
        -> coe
             d_numAt_60 (coe v0) (coe v2)
             (coe MAlonzo.Code.Once.Spec.Float.Value.d_odd_34 (coe v3)) (coe v4)
             (coe
                MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v4)
                (coe
                   addInt (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_bias_58 (coe v0))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                      (MAlonzo.Code.Once.Spec.Float.Dyadic.d_bitLen_74
                         (coe MAlonzo.Code.Once.Spec.Float.Value.d_odd_34 (coe v3)))
                      (1 :: Integer))))
      MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'inf_30 v2
        -> coe d_infW_24 (coe v0) (coe v2)
      MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'nan_32
        -> coe d_nanW_30 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Encoding.signOf
d_signOf_108 ::
  Integer -> MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8
d_signOf_108 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Once.Spec.Float.Value.C_pos_10
      _ -> coe MAlonzo.Code.Once.Spec.Float.Value.C_neg_12
-- Once.Spec.Float.Encoding.decodeMax
d_decodeMax_110 ::
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer -> MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24
d_decodeMax_110 v0 v1
  = case coe v1 of
      0 -> coe MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'inf_30 (coe v0)
      _ -> coe MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'nan_32
-- Once.Spec.Float.Encoding.decodeAt
d_decodeAt_116 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer ->
  Integer ->
  Bool -> Bool -> MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24
d_decodeAt_116 v0 v1 v2 v3 v4 v5
  = if coe v4
      then coe
             MAlonzo.Code.Once.Spec.Float.Value.d_canon_84 (coe v3) (coe v1)
             (coe v3)
             (coe MAlonzo.Code.Once.Spec.Float.Value.d_qmin_66 (coe v0))
      else (if coe v5
              then coe d_decodeMax_110 (coe v1) (coe v3)
              else coe
                     MAlonzo.Code.Once.Spec.Float.Value.d_canon_84
                     (coe
                        addInt
                        (coe
                           MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                           (coe
                              MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_40 (coe v0)))
                        (coe v3))
                     (coe v1)
                     (coe
                        addInt
                        (coe
                           MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                           (coe
                              MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_40 (coe v0)))
                        (coe v3))
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v2)
                        (coe
                           addInt (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_bias_58 (coe v0))
                           (coe
                              MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_40 (coe v0)))))
-- Once.Spec.Float.Encoding.decode
d_decode_142 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24
d_decode_142 v0 v1
  = coe
      d_decodeAt_116 (coe v0)
      (coe
         d_signOf_108
         (coe
            MAlonzo.Code.Data.Nat.Base.du__'47'__318
            (coe
               MAlonzo.Code.Once.Spec.Float.Dyadic.d_modPow_62 (coe v1)
               (coe
                  addInt
                  (coe
                     addInt (coe (1 :: Integer))
                     (coe
                        MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_42 (coe v0)))
                  (coe
                     MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_40 (coe v0))))
            (coe d_signWeight_10 (coe v0))))
      (coe
         MAlonzo.Code.Data.Nat.Base.du__'47'__318
         (coe
            MAlonzo.Code.Once.Spec.Float.Dyadic.d_modPow_62 (coe v1)
            (coe
               addInt
               (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_42 (coe v0))
               (coe
                  MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_40 (coe v0))))
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe
               MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_40 (coe v0))))
      (coe
         MAlonzo.Code.Once.Spec.Float.Dyadic.d_modPow_62 (coe v1)
         (coe
            MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_40 (coe v0)))
      (coe
         eqInt
         (coe
            MAlonzo.Code.Data.Nat.Base.du__'47'__318
            (coe
               MAlonzo.Code.Once.Spec.Float.Dyadic.d_modPow_62 (coe v1)
               (coe
                  addInt
                  (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_42 (coe v0))
                  (coe
                     MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_40 (coe v0))))
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
               (coe
                  MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_40 (coe v0))))
         (coe (0 :: Integer)))
      (coe
         eqInt
         (coe
            MAlonzo.Code.Data.Nat.Base.du__'47'__318
            (coe
               MAlonzo.Code.Once.Spec.Float.Dyadic.d_modPow_62 (coe v1)
               (coe
                  addInt
                  (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_42 (coe v0))
                  (coe
                     MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_40 (coe v0))))
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
               (coe
                  MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_40 (coe v0))))
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
            (MAlonzo.Code.Data.Nat.Base.d__'94'__276
               (coe (2 :: Integer))
               (coe
                  MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_42 (coe v0)))
            (1 :: Integer)))
