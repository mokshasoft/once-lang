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

module MAlonzo.Code.Once.Float.Word where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Spec.Float.Arith
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic
import qualified MAlonzo.Code.Once.Spec.Float.Encoding
import qualified MAlonzo.Code.Once.Spec.Float.Value

-- Once.Float.Word.onWords
d_onWords_6 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  (MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 ->
   MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 ->
   MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24) ->
  Integer -> Integer -> Integer
d_onWords_6 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Float.Encoding.d_encode_88 (coe v0)
      (coe
         v1
         (MAlonzo.Code.Once.Spec.Float.Encoding.d_decode_142
            (coe v0) (coe v2))
         (MAlonzo.Code.Once.Spec.Float.Encoding.d_decode_142
            (coe v0) (coe v3)))
-- Once.Float.Word.fadd
d_fadd_16 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer
d_fadd_16 v0
  = coe
      d_onWords_6 (coe v0)
      (coe MAlonzo.Code.Once.Spec.Float.Arith.d_addV_294 (coe v0))
-- Once.Float.Word.fsub
d_fsub_18 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer
d_fsub_18 v0
  = coe
      d_onWords_6 (coe v0)
      (coe
         (\ v1 v2 ->
            MAlonzo.Code.Once.Spec.Float.Arith.d_addV_294
              (coe v0) (coe v1)
              (coe MAlonzo.Code.Once.Spec.Float.Value.d_negV_38 (coe v2))))
-- Once.Float.Word.fmul
d_fmul_20 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer
d_fmul_20 v0
  = coe
      d_onWords_6 (coe v0)
      (coe MAlonzo.Code.Once.Spec.Float.Arith.d_mulV_296 (coe v0))
-- Once.Float.Word.fdiv
d_fdiv_22 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer
d_fdiv_22 v0
  = coe
      d_onWords_6 (coe v0)
      (coe MAlonzo.Code.Once.Spec.Float.Arith.d_divV_298 (coe v0))
-- Once.Float.Word.fnegAt
d_fnegAt_36 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Bool -> Integer
d_fnegAt_36 v0 v1 v2
  = if coe v2
      then coe
             MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1
             (MAlonzo.Code.Data.Nat.Base.d__'94'__276
                (coe (2 :: Integer))
                (coe
                   addInt
                   (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_42 (coe v0))
                   (coe
                      MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_40 (coe v0))))
      else coe
             addInt
             (coe
                MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                (coe
                   addInt
                   (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_42 (coe v0))
                   (coe
                      MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_40 (coe v0))))
             (coe v1)
-- Once.Float.Word.fneg
d_fneg_46 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer
d_fneg_46 v0 v1
  = coe
      d_fnegAt_36 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe
               addInt
               (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_42 (coe v0))
               (coe
                  MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_40 (coe v0))))
         (coe v1))
-- Once.Float.Word.i2f
d_i2f_52 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer
d_i2f_52 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Float.Encoding.d_encode_88 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Float.Arith.d_i2fV_324 (coe v0) (coe v1))
-- Once.Float.Word.round
d_round_58 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Spec.Float.Decimal.T_Decimal_8 -> Integer
d_round_58 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Float.Encoding.d_encode_88 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Float.Decimal.d_roundDec_38 (coe v0)
         (coe v1))
-- Once.Float.Word.nan
d_nan_64 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 -> Integer
d_nan_64 = coe MAlonzo.Code.Once.Spec.Float.Encoding.d_nanW_30
-- Once.Float.Word.fit
d_fit_66 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer
d_fit_66 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Float.Encoding.d_encode_88 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Float.Value.d_fitV_228 (coe v0)
         (coe
            MAlonzo.Code.Once.Spec.Float.Encoding.d_decode_142 (coe v0)
            (coe v1)))
