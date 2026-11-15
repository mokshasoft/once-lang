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

module MAlonzo.Code.Once.Spec.Float.Value where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic

-- Once.Spec.Float.Value.Sign
d_Sign_8 = ()
data T_Sign_8 = C_pos_10 | C_neg_12
-- Once.Spec.Float.Value.flip
d_flip_14 :: T_Sign_8 -> T_Sign_8
d_flip_14 v0
  = case coe v0 of
      C_pos_10 -> coe C_neg_12
      C_neg_12 -> coe C_pos_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Value.xorS
d_xorS_16 :: T_Sign_8 -> T_Sign_8 -> T_Sign_8
d_xorS_16 v0 v1
  = case coe v0 of
      C_pos_10 -> coe v1
      C_neg_12 -> coe d_flip_14 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Value.sameS
d_sameS_22 :: T_Sign_8 -> T_Sign_8 -> Bool
d_sameS_22 v0 v1
  = case coe v0 of
      C_pos_10
        -> case coe v1 of
             C_pos_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             C_neg_12 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_neg_12
        -> case coe v1 of
             C_pos_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_neg_12 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Value.FloatVal
d_FloatVal_24 = ()
data T_FloatVal_24
  = C_fv'45'zero_26 T_Sign_8 |
    C_fv'45'num_28 T_Sign_8 Integer Integer | C_fv'45'inf_30 T_Sign_8 |
    C_fv'45'nan_32
-- Once.Spec.Float.Value.odd
d_odd_34 :: Integer -> Integer
d_odd_34 v0
  = coe
      addInt (coe (1 :: Integer))
      (coe mulInt (coe (2 :: Integer)) (coe v0))
-- Once.Spec.Float.Value.negV
d_negV_38 :: T_FloatVal_24 -> T_FloatVal_24
d_negV_38 v0
  = case coe v0 of
      C_fv'45'zero_26 v1 -> coe C_fv'45'zero_26 (coe d_flip_14 (coe v1))
      C_fv'45'num_28 v1 v2 v3
        -> coe C_fv'45'num_28 (coe d_flip_14 (coe v1)) (coe v2) (coe v3)
      C_fv'45'inf_30 v1 -> coe C_fv'45'inf_30 (coe d_flip_14 (coe v1))
      C_fv'45'nan_32 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Value.roundHalfEven
d_roundHalfEven_50 :: Integer -> Integer -> Integer -> Integer
d_roundHalfEven_50 v0 v1 v2
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
-- Once.Spec.Float.Value.divRHE
d_divRHE_60 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_divRHE_60 v0 v1 ~v2 = du_divRHE_60 v0 v1
du_divRHE_60 :: Integer -> Integer -> Integer
du_divRHE_60 v0 v1
  = coe
      d_roundHalfEven_50
      (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1))
      (coe MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v0) (coe v1))
      (coe v1)
-- Once.Spec.Float.Value.qmin
d_qmin_66 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 -> Integer
d_qmin_66 v0
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe (1 :: Integer))
      (coe
         addInt (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_bias_58 (coe v0))
         (coe
            MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_40 (coe v0)))
-- Once.Spec.Float.Value.quantum
d_quantum_70 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer
d_quantum_70 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'8852'__330
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v1)
         (coe
            MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_40 (coe v0)))
      (coe d_qmin_66 (coe v0))
-- Once.Spec.Float.Value.overflows
d_overflows_76 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Bool
d_overflows_76 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110
      (coe
         addInt (coe (2 :: Integer))
         (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_bias_58 (coe v0)))
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'43'__284
         (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_bitLen_74 (coe v1))
         (coe v2))
-- Once.Spec.Float.Value.canon
d_canon_84 ::
  Integer -> T_Sign_8 -> Integer -> Integer -> T_FloatVal_24
d_canon_84 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe C_fv'45'zero_26 (coe v1)
      _ -> case coe v0 of
             0 -> coe
                    C_fv'45'num_28 (coe v1)
                    (coe
                       MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v2)
                       (coe (2 :: Integer)))
                    (coe v3)
             _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
                  coe
                    (coe
                       d_canonAt_86 (coe v4) (coe v1) (coe v2) (coe v3)
                       (coe
                          eqInt
                          (coe
                             MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v2)
                             (coe (2 :: Integer)))
                          (coe (1 :: Integer))))
-- Once.Spec.Float.Value.canonAt
d_canonAt_86 ::
  Integer -> T_Sign_8 -> Integer -> Integer -> Bool -> T_FloatVal_24
d_canonAt_86 v0 v1 v2 v3 v4
  = if coe v4
      then coe
             C_fv'45'num_28 (coe v1)
             (coe
                MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v2)
                (coe (2 :: Integer)))
             (coe v3)
      else coe
             d_canon_84 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v2)
                (coe (2 :: Integer)))
             (coe
                MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v3)
                (coe (1 :: Integer)))
-- Once.Spec.Float.Value.finish
d_finish_124 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  T_Sign_8 -> Integer -> Integer -> T_FloatVal_24
d_finish_124 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe C_fv'45'zero_26 (coe v1)
      _ -> coe
             d_finishAt_126 (coe v1) (coe v2) (coe v3)
             (coe d_overflows_76 (coe v0) (coe v2) (coe v3))
-- Once.Spec.Float.Value.finishAt
d_finishAt_126 ::
  T_Sign_8 -> Integer -> Integer -> Bool -> T_FloatVal_24
d_finishAt_126 v0 v1 v2 v3
  = if coe v3
      then coe C_fv'45'inf_30 (coe v0)
      else coe d_canon_84 (coe v1) (coe v0) (coe v1) (coe v2)
-- Once.Spec.Float.Value.atLeast
d_atLeast_154 :: Integer -> Integer -> Integer -> Bool
d_atLeast_154 v0 v1 v2
  = case coe v2 of
      _ | coe geqInt (coe v2) (coe (0 :: Integer)) ->
          coe
            MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
            (coe
               mulInt (coe v1)
               (coe
                  MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                  (coe v2)))
            (coe v0)
      _ -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v1)
             (coe
                mulInt (coe v0)
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                   (coe subInt (coe (0 :: Integer)) (coe v2))))
-- Once.Spec.Float.Value.lgAt
d_lgAt_168 :: Integer -> Bool -> Integer
d_lgAt_168 v0 v1
  = if coe v1
      then coe v0
      else coe
             MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v0)
             (coe (1 :: Integer))
-- Once.Spec.Float.Value.lg
d_lg_174 :: Integer -> Integer -> Integer
d_lg_174 v0 v1
  = coe
      d_lgAt_168
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'45'__302
         (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_bitLen_74 (coe v0))
         (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_bitLen_74 (coe v1)))
      (coe
         d_atLeast_154 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'45'__302
            (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_bitLen_74 (coe v0))
            (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_bitLen_74 (coe v1))))
-- Once.Spec.Float.Value.scaleRHE
d_scaleRHE_180 :: Integer -> Integer -> Integer -> Integer
d_scaleRHE_180 v0 v1 v2
  = case coe v2 of
      _ | coe geqInt (coe v2) (coe (0 :: Integer)) ->
          coe
            du_divRHE_60
            (coe
               mulInt (coe v0)
               (coe
                  MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                  (coe v2)))
            (coe addInt (coe (1 :: Integer)) (coe v1))
      _ -> coe
             du_divRHE_60 (coe v0)
             (coe
                mulInt (coe addInt (coe (1 :: Integer)) (coe v1))
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                   (coe subInt (coe (0 :: Integer)) (coe v2))))
-- Once.Spec.Float.Value.roundAt
d_roundAt_194 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  T_Sign_8 ->
  Integer -> Integer -> Integer -> Integer -> T_FloatVal_24
d_roundAt_194 v0 v1 v2 v3 v4 v5
  = coe
      d_finish_124 (coe v0) (coe v1)
      (coe
         d_scaleRHE_180 (coe v2) (coe v4)
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v3) (coe v5)))
      (coe v5)
-- Once.Spec.Float.Value.roundQ
d_roundQ_208 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  T_Sign_8 -> Integer -> Integer -> Integer -> T_FloatVal_24
d_roundQ_208 v0 v1 v2 v3 v4
  = case coe v2 of
      0 -> coe C_fv'45'zero_26 (coe v1)
      _ -> coe
             d_roundAt_194 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe
                d_quantum_70 (coe v0)
                (coe
                   MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v3)
                   (coe
                      d_lg_174 (coe v2) (coe addInt (coe (1 :: Integer)) (coe v4)))))
-- Once.Spec.Float.Value.fitV
d_fitV_228 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  T_FloatVal_24 -> T_FloatVal_24
d_fitV_228 v0 v1
  = case coe v1 of
      C_fv'45'zero_26 v2 -> coe v1
      C_fv'45'num_28 v2 v3 v4
        -> coe
             d_roundQ_208 (coe v0) (coe v2) (coe d_odd_34 (coe v3)) (coe v4)
             (coe (0 :: Integer))
      C_fv'45'inf_30 v2 -> coe v1
      C_fv'45'nan_32 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Value.Fits
d_Fits_248 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  T_FloatVal_24 -> ()
d_Fits_248 = erased
