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
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic
import qualified MAlonzo.Code.Once.Spec.Float.Value

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
-- Once.Spec.Float.Decimal.roundDec
d_roundDec_38 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  T_Decimal_8 -> MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24
d_roundDec_38 v0 v1
  = case coe v1 of
      C__'47'10'94'__18 v2 v3
        -> case coe v2 of
             _ | coe geqInt (coe v2) (coe (0 :: Integer)) ->
                 coe
                   MAlonzo.Code.Once.Spec.Float.Value.d_roundQ_208 (coe v0)
                   (coe MAlonzo.Code.Once.Spec.Float.Value.C_pos_10) (coe v2)
                   (coe (0 :: Integer))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                      (MAlonzo.Code.Data.Nat.Base.d__'94'__276
                         (coe (10 :: Integer)) (coe v3))
                      (1 :: Integer))
             _ -> coe
                    MAlonzo.Code.Once.Spec.Float.Value.d_roundQ_208 (coe v0)
                    (coe MAlonzo.Code.Once.Spec.Float.Value.C_neg_12)
                    (coe subInt (coe (0 :: Integer)) (coe v2)) (coe (0 :: Integer))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                       (MAlonzo.Code.Data.Nat.Base.d__'94'__276
                          (coe (10 :: Integer)) (coe v3))
                       (1 :: Integer))
      _ -> MAlonzo.RTE.mazUnreachableError
