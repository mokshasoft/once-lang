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

module MAlonzo.Code.Once.Spec.Float.Arith where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic
import qualified MAlonzo.Code.Once.Spec.Float.Value

-- Once.Spec.Float.Arith.Operand
d_Operand_8 = ()
data T_Operand_8
  = C_inf_10 MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 |
    C_fin_12 MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 Integer
             Integer
-- Once.Spec.Float.Arith.exact
d_exact_14 ::
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 ->
  Maybe T_Operand_8
d_exact_14 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'zero_26 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_fin_12 (coe v1) (coe (0 :: Integer)) (coe (0 :: Integer)))
      MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'num_28 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_fin_12 (coe v1)
                (coe MAlonzo.Code.Once.Spec.Float.Value.d_odd_34 (coe v2))
                (coe v3))
      MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'inf_30 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_inf_10 (coe v1))
      MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'nan_32
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Arith.both
d_both_28 ::
  () ->
  AgdaAny ->
  (T_Operand_8 -> T_Operand_8 -> AgdaAny) ->
  Maybe T_Operand_8 -> Maybe T_Operand_8 -> AgdaAny
d_both_28 ~v0 v1 v2 v3 v4 = du_both_28 v1 v2 v3 v4
du_both_28 ::
  AgdaAny ->
  (T_Operand_8 -> T_Operand_8 -> AgdaAny) ->
  Maybe T_Operand_8 -> Maybe T_Operand_8 -> AgdaAny
du_both_28 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5 -> coe v1 v4 v5
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Arith.onNumbers
d_onNumbers_48 ::
  () ->
  AgdaAny ->
  (T_Operand_8 -> T_Operand_8 -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 -> AgdaAny
d_onNumbers_48 ~v0 v1 v2 v3 v4 = du_onNumbers_48 v1 v2 v3 v4
du_onNumbers_48 ::
  AgdaAny ->
  (T_Operand_8 -> T_Operand_8 -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 -> AgdaAny
du_onNumbers_48 v0 v1 v2 v3
  = coe
      du_both_28 (coe v0) (coe v1) (coe d_exact_14 (coe v2))
      (coe d_exact_14 (coe v3))
-- Once.Spec.Float.Arith.Exact
d_Exact_58 = ()
data T_Exact_58
  = C_invalid_60 |
    C_'8734'_62 MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 |
    C_ratio_64 MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 Integer
               Integer Integer
-- Once.Spec.Float.Arith.round
d_round_66 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  T_Exact_58 -> MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24
d_round_66 v0 v1
  = case coe v1 of
      C_invalid_60
        -> coe MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'nan_32
      C_'8734'_62 v2
        -> coe MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'inf_30 (coe v2)
      C_ratio_64 v2 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Float.Value.d_roundQ_208 (coe v0) (coe v2)
             (coe v3) (coe v4) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Arith.exactOf
d_exactOf_84 :: Maybe T_Operand_8 -> T_Exact_58
d_exactOf_84 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             C_inf_10 v2 -> coe C_'8734'_62 (coe v2)
             C_fin_12 v2 v3 v4
               -> coe C_ratio_64 (coe v2) (coe v3) (coe v4) (coe (0 :: Integer))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe C_invalid_60
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Arith.negO
d_negO_94 :: T_Operand_8 -> T_Operand_8
d_negO_94 v0
  = case coe v0 of
      C_inf_10 v1
        -> coe
             C_inf_10
             (coe MAlonzo.Code.Once.Spec.Float.Value.d_flip_14 (coe v1))
      C_fin_12 v1 v2 v3
        -> coe
             C_fin_12
             (coe MAlonzo.Code.Once.Spec.Float.Value.d_flip_14 (coe v1))
             (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Arith.negE
d_negE_104 :: T_Exact_58 -> T_Exact_58
d_negE_104 v0
  = case coe v0 of
      C_invalid_60 -> coe v0
      C_'8734'_62 v1
        -> coe
             C_'8734'_62
             (coe MAlonzo.Code.Once.Spec.Float.Value.d_flip_14 (coe v1))
      C_ratio_64 v1 v2 v3 v4
        -> coe
             C_ratio_64
             (coe MAlonzo.Code.Once.Spec.Float.Value.d_flip_14 (coe v1))
             (coe v2) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Arith.alignTo
d_alignTo_116 :: Integer -> Integer -> Integer -> Integer
d_alignTo_116 v0 v1 v2
  = coe
      mulInt (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
         (coe
            MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
            (coe
               MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v1) (coe v2))))
-- Once.Spec.Float.Arith.cancel
d_cancel_124 ::
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer -> Integer -> Bool -> Bool -> T_Exact_58
d_cancel_124 v0 v1 v2 v3 v4 v5 v6
  = if coe v5
      then coe
             C_ratio_64 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v3 v1) (coe v4)
             (coe (0 :: Integer))
      else (if coe v6
              then coe
                     C_ratio_64 (coe v0)
                     (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 v3) (coe v4)
                     (coe (0 :: Integer))
              else coe
                     C_ratio_64 (coe MAlonzo.Code.Once.Spec.Float.Value.C_pos_10)
                     (coe (0 :: Integer)) (coe v4) (coe (0 :: Integer)))
-- Once.Spec.Float.Arith.addAt
d_addAt_156 ::
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer -> Integer -> Bool -> T_Exact_58
d_addAt_156 v0 v1 v2 v3 v4 v5
  = if coe v5
      then coe
             C_ratio_64 (coe v0) (coe addInt (coe v1) (coe v3)) (coe v4)
             (coe (0 :: Integer))
      else coe
             d_cancel_124 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe ltInt (coe v1) (coe v3)) (coe ltInt (coe v3) (coe v1))
-- Once.Spec.Float.Arith.infAdd
d_infAdd_178 ::
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 -> Bool -> T_Exact_58
d_infAdd_178 v0 ~v1 v2 = du_infAdd_178 v0 v2
du_infAdd_178 ::
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 -> Bool -> T_Exact_58
du_infAdd_178 v0 v1
  = if coe v1 then coe C_'8734'_62 (coe v0) else coe C_invalid_60
-- Once.Spec.Float.Arith.addE
d_addE_188 :: T_Operand_8 -> T_Operand_8 -> T_Exact_58
d_addE_188 v0 v1
  = case coe v0 of
      C_inf_10 v2
        -> case coe v1 of
             C_inf_10 v3
               -> coe
                    du_infAdd_178 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Value.d_sameS_22 (coe v2) (coe v3))
             C_fin_12 v3 v4 v5 -> coe C_'8734'_62 (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fin_12 v2 v3 v4
        -> case coe v1 of
             C_inf_10 v5 -> coe C_'8734'_62 (coe v5)
             C_fin_12 v5 v6 v7
               -> coe
                    d_addAt_156 (coe v2)
                    (coe
                       d_alignTo_116 (coe v3) (coe v4)
                       (coe
                          MAlonzo.Code.Data.Integer.Base.d__'8851'__348 (coe v4) (coe v7)))
                    (coe v5)
                    (coe
                       d_alignTo_116 (coe v6) (coe v7)
                       (coe
                          MAlonzo.Code.Data.Integer.Base.d__'8851'__348 (coe v4) (coe v7)))
                    (coe
                       MAlonzo.Code.Data.Integer.Base.d__'8851'__348 (coe v4) (coe v7))
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Value.d_sameS_22 (coe v2) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Arith.infMul
d_infMul_210 ::
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer -> T_Exact_58
d_infMul_210 v0 v1
  = case coe v1 of
      0 -> coe C_invalid_60
      _ -> coe C_'8734'_62 (coe v0)
-- Once.Spec.Float.Arith.mulE
d_mulE_216 :: T_Operand_8 -> T_Operand_8 -> T_Exact_58
d_mulE_216 v0 v1
  = case coe v0 of
      C_inf_10 v2
        -> case coe v1 of
             C_inf_10 v3
               -> coe
                    C_'8734'_62
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Value.d_xorS_16 (coe v2) (coe v3))
             C_fin_12 v3 v4 v5
               -> coe
                    d_infMul_210
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Value.d_xorS_16 (coe v2) (coe v3))
                    (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fin_12 v2 v3 v4
        -> case coe v1 of
             C_inf_10 v5
               -> coe
                    d_infMul_210
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Value.d_xorS_16 (coe v2) (coe v5))
                    (coe v3)
             C_fin_12 v5 v6 v7
               -> coe
                    C_ratio_64
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Value.d_xorS_16 (coe v2) (coe v5))
                    (coe mulInt (coe v3) (coe v6))
                    (coe MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v4) (coe v7))
                    (coe (0 :: Integer))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Arith.finDiv
d_finDiv_246 ::
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer -> Integer -> Integer -> Integer -> T_Exact_58
d_finDiv_246 v0 v1 v2 v3 v4
  = case coe v1 of
      0 -> case coe v2 of
             0 -> coe C_invalid_60
             _ -> coe C_'8734'_62 (coe v0)
      _ -> let v5 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                C_ratio_64 (coe v0) (coe v2)
                (coe MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v3) (coe v4))
                (coe v5))
-- Once.Spec.Float.Arith.divE
d_divE_272 :: T_Operand_8 -> T_Operand_8 -> T_Exact_58
d_divE_272 v0 v1
  = case coe v0 of
      C_inf_10 v2
        -> case coe v1 of
             C_inf_10 v3 -> coe C_invalid_60
             C_fin_12 v3 v4 v5
               -> coe
                    C_'8734'_62
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Value.d_xorS_16 (coe v2) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fin_12 v2 v3 v4
        -> case coe v1 of
             C_inf_10 v5
               -> coe
                    C_ratio_64
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Value.d_xorS_16 (coe v2) (coe v5))
                    (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
             C_fin_12 v5 v6 v7
               -> coe
                    d_finDiv_246
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Value.d_xorS_16 (coe v2) (coe v5))
                    (coe v6) (coe v3) (coe v4) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Arith.addV
d_addV_294 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24
d_addV_294 v0 v1 v2
  = coe
      d_round_66 (coe v0)
      (coe
         du_onNumbers_48 (coe C_invalid_60) (coe d_addE_188) (coe v1)
         (coe v2))
-- Once.Spec.Float.Arith.mulV
d_mulV_296 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24
d_mulV_296 v0 v1 v2
  = coe
      d_round_66 (coe v0)
      (coe
         du_onNumbers_48 (coe C_invalid_60) (coe d_mulE_216) (coe v1)
         (coe v2))
-- Once.Spec.Float.Arith.divV
d_divV_298 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24
d_divV_298 v0 v1 v2
  = coe
      d_round_66 (coe v0)
      (coe
         du_onNumbers_48 (coe C_invalid_60) (coe d_divE_272) (coe v1)
         (coe v2))
-- Once.Spec.Float.Arith.fromℤ
d_fromℤ_318 :: Integer -> T_Exact_58
d_fromℤ_318 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe
            C_ratio_64 (coe MAlonzo.Code.Once.Spec.Float.Value.C_pos_10)
            (coe v0) (coe (0 :: Integer)) (coe (0 :: Integer))
      _ -> coe
             C_ratio_64 (coe MAlonzo.Code.Once.Spec.Float.Value.C_neg_12)
             (coe subInt (coe (0 :: Integer)) (coe v0)) (coe (0 :: Integer))
             (coe (0 :: Integer))
-- Once.Spec.Float.Arith.i2fV
d_i2fV_324 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24
d_i2fV_324 v0 v1
  = coe d_round_66 (coe v0) (coe d_fromℤ_318 (coe v1))
-- Once.Spec.Float.Arith.signedAt
d_signedAt_330 ::
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer -> Integer -> Integer -> Integer
d_signedAt_330 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Float.Value.C_pos_10
        -> coe d_alignTo_116 (coe v1) (coe v2) (coe v3)
      MAlonzo.Code.Once.Spec.Float.Value.C_neg_12
        -> coe
             MAlonzo.Code.Data.Integer.Base.d_'45'__260
             (coe d_alignTo_116 (coe v1) (coe v2) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Arith.ltR
d_ltR_344 :: T_Operand_8 -> T_Operand_8 -> Bool
d_ltR_344 v0 v1
  = case coe v0 of
      C_inf_10 v2
        -> case coe v1 of
             C_inf_10 v3
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Value.d_sameS_22 (coe v2)
                       (coe MAlonzo.Code.Once.Spec.Float.Value.C_neg_12))
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Value.d_sameS_22 (coe v3)
                       (coe MAlonzo.Code.Once.Spec.Float.Value.C_pos_10))
             C_fin_12 v3 v4 v5
               -> coe
                    MAlonzo.Code.Once.Spec.Float.Value.d_sameS_22 (coe v2)
                    (coe MAlonzo.Code.Once.Spec.Float.Value.C_neg_12)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fin_12 v2 v3 v4
        -> case coe v1 of
             C_inf_10 v5
               -> coe
                    MAlonzo.Code.Once.Spec.Float.Value.d_sameS_22 (coe v5)
                    (coe MAlonzo.Code.Once.Spec.Float.Value.C_pos_10)
             C_fin_12 v5 v6 v7
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d_not_22
                    (coe
                       MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110
                       (coe
                          d_signedAt_330 (coe v5) (coe v6) (coe v7)
                          (coe
                             MAlonzo.Code.Data.Integer.Base.d__'8851'__348 (coe v4) (coe v7)))
                       (coe
                          d_signedAt_330 (coe v2) (coe v3) (coe v4)
                          (coe
                             MAlonzo.Code.Data.Integer.Base.d__'8851'__348 (coe v4) (coe v7))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Arith.isNaN
d_isNaN_366 ::
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 -> Bool
d_isNaN_366 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'zero_26 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'num_28 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'inf_30 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'nan_32
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Arith.isZeroOf
d_isZeroOf_368 ::
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 -> Bool
d_isZeroOf_368 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'zero_26 v2
        -> coe
             MAlonzo.Code.Once.Spec.Float.Value.d_sameS_22 (coe v0) (coe v2)
      MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'num_28 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'inf_30 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'nan_32
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Arith.eqR
d_eqR_380 :: T_Operand_8 -> T_Operand_8 -> Bool
d_eqR_380 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      (coe
         MAlonzo.Code.Data.Bool.Base.d_not_22
         (coe d_ltR_344 (coe v0) (coe v1)))
      (coe
         MAlonzo.Code.Data.Bool.Base.d_not_22
         (coe d_ltR_344 (coe v1) (coe v0)))
-- Once.Spec.Float.Arith.eqQ
d_eqQ_386 ::
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 -> Bool
d_eqQ_386
  = coe
      du_onNumbers_48 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe d_eqR_380)
-- Once.Spec.Float.Arith.ltQ
d_ltQ_388 ::
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 -> Bool
d_ltQ_388
  = coe
      du_onNumbers_48 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe d_ltR_344)
-- Once.Spec.Float.Arith.ltT
d_ltT_390 ::
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 -> Bool
d_ltT_390 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30 (coe d_ltQ_388 v0 v1)
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8744'__30
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8743'__24
            (coe
               d_isZeroOf_368 (coe MAlonzo.Code.Once.Spec.Float.Value.C_neg_12)
               (coe v0))
            (coe
               d_isZeroOf_368 (coe MAlonzo.Code.Once.Spec.Float.Value.C_pos_10)
               (coe v1)))
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8743'__24
            (coe
               MAlonzo.Code.Data.Bool.Base.d_not_22 (coe d_isNaN_366 (coe v0)))
            (coe d_isNaN_366 (coe v1))))
-- Once.Spec.Float.Arith.eqV
d_eqV_396 ::
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 -> Bool
d_eqV_396 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      (coe
         MAlonzo.Code.Data.Bool.Base.d_not_22
         (coe d_ltT_390 (coe v0) (coe v1)))
      (coe
         MAlonzo.Code.Data.Bool.Base.d_not_22
         (coe d_ltT_390 (coe v1) (coe v0)))
