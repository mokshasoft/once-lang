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
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic
import qualified MAlonzo.Code.Once.Spec.Float.Value

-- Once.Spec.Float.Decimal.Decimal
d_Decimal_8 = ()
data T_Decimal_8
  = C_'10216'_'10217'_'47'10'94'__22 MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8
                                     Integer Integer
-- Once.Spec.Float.Decimal.Decimal.sign
d_sign_16 ::
  T_Decimal_8 -> MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8
d_sign_16 v0
  = case coe v0 of
      C_'10216'_'10217'_'47'10'94'__22 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Decimal.Decimal.sig
d_sig_18 :: T_Decimal_8 -> Integer
d_sig_18 v0
  = case coe v0 of
      C_'10216'_'10217'_'47'10'94'__22 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Decimal.Decimal.exp10
d_exp10_20 :: T_Decimal_8 -> Integer
d_exp10_20 v0
  = case coe v0 of
      C_'10216'_'10217'_'47'10'94'__22 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Decimal.fromℕ
d_fromℕ_24 :: Integer -> T_Decimal_8
d_fromℕ_24 v0
  = coe
      C_'10216'_'10217'_'47'10'94'__22
      (coe MAlonzo.Code.Once.Spec.Float.Value.C_pos_10) (coe v0)
      (coe (0 :: Integer))
-- Once.Spec.Float.Decimal.roundDec
d_roundDec_28 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  T_Decimal_8 -> MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24
d_roundDec_28 v0 v1
  = case coe v1 of
      C_'10216'_'10217'_'47'10'94'__22 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Float.Value.d_roundQ_208 (coe v0) (coe v2)
             (coe v3) (coe (0 :: Integer))
             (coe
                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                (MAlonzo.Code.Data.Nat.Base.d__'94'__276
                   (coe (10 :: Integer)) (coe v4))
                (1 :: Integer))
      _ -> MAlonzo.RTE.mazUnreachableError
