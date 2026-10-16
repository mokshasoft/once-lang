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
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic

-- Once.Spec.Float.Arith.Bin
d_Bin_8 = ()
data T_Bin_8 = C__'183'2'94'__18 Integer Integer
-- Once.Spec.Float.Arith.Bin.sigB
d_sigB_14 :: T_Bin_8 -> Integer
d_sigB_14 v0
  = case coe v0 of
      C__'183'2'94'__18 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Arith.Bin.expB
d_expB_16 :: T_Bin_8 -> Integer
d_expB_16 v0
  = case coe v0 of
      C__'183'2'94'__18 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Arith.addAt
d_addAt_20 ::
  Integer -> Integer -> Integer -> Integer -> Integer -> T_Bin_8
d_addAt_20 v0 v1 v2 v3 v4
  = coe
      C__'183'2'94'__18
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'43'__284
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0)
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
               (coe
                  MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v1) (coe v4)))))
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v2)
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
               (coe
                  MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v3) (coe v4))))))
      (coe v4)
-- Once.Spec.Float.Arith._+B_
d__'43'B__32 :: T_Bin_8 -> T_Bin_8 -> T_Bin_8
d__'43'B__32 v0 v1
  = coe
      d_addAt_20 (coe d_sigB_14 (coe v0)) (coe d_expB_16 (coe v0))
      (coe d_sigB_14 (coe v1)) (coe d_expB_16 (coe v1))
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'8851'__348
         (coe d_expB_16 (coe v0)) (coe d_expB_16 (coe v1)))
-- Once.Spec.Float.Arith._*B_
d__'42'B__38 :: T_Bin_8 -> T_Bin_8 -> T_Bin_8
d__'42'B__38 v0 v1
  = coe
      C__'183'2'94'__18
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'42'__316
         (coe d_sigB_14 (coe v0)) (coe d_sigB_14 (coe v1)))
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'43'__284
         (coe d_expB_16 (coe v0)) (coe d_expB_16 (coe v1)))
-- Once.Spec.Float.Arith.negB
d_negB_44 :: T_Bin_8 -> T_Bin_8
d_negB_44 v0
  = coe
      C__'183'2'94'__18
      (coe
         MAlonzo.Code.Data.Integer.Base.d_'45'__260
         (coe d_sigB_14 (coe v0)))
      (coe d_expB_16 (coe v0))
-- Once.Spec.Float.Arith.isZeroB
d_isZeroB_48 :: T_Bin_8 -> Bool
d_isZeroB_48 v0
  = coe
      eqInt
      (coe
         MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
         (coe d_sigB_14 (coe v0)))
      (coe (0 :: Integer))
-- Once.Spec.Float.Arith.signB
d_signB_52 :: T_Bin_8 -> Integer
d_signB_52 v0
  = coe
      MAlonzo.Code.Once.Spec.Float.Dyadic.d_signBit_70
      (coe d_sigB_14 (coe v0))
-- Once.Spec.Float.Arith.FloatVal
d_FloatVal_56 = ()
data T_FloatVal_56
  = C_fv'45'fin_58 T_Bin_8 | C_fv'45'inf_60 Integer | C_fv'45'nan_62
-- Once.Spec.Float.Arith.applySign
d_applySign_64 :: Integer -> Integer -> Integer
d_applySign_64 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v0) (coe (0 :: Integer))) (coe v1)
      (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1))
-- Once.Spec.Float.Arith.normExp
d_normExp_70 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer
d_normExp_70 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v1)
      (coe
         addInt (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_bias_50 (coe v0))
         (coe
            MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0)))
-- Once.Spec.Float.Arith.subExp
d_subExp_76 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 -> Integer
d_subExp_76 v0
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe (1 :: Integer))
      (coe
         addInt (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_bias_50 (coe v0))
         (coe
            MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0)))
-- Once.Spec.Float.Arith.nan
d_nan_80 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 -> Integer
d_nan_80 v0
  = coe
      addInt
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
            (MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0))
            (1 :: Integer)))
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
-- Once.Spec.Float.Arith.decodeMax
d_decodeMax_84 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> T_FloatVal_56
d_decodeMax_84 ~v0 v1 v2 = du_decodeMax_84 v1 v2
du_decodeMax_84 :: Integer -> Integer -> T_FloatVal_56
du_decodeMax_84 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v1) (coe (0 :: Integer)))
      (coe C_fv'45'inf_60 (coe v0)) (coe C_fv'45'nan_62)
-- Once.Spec.Float.Arith.decodeAt
d_decodeAt_92 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer -> Bool -> Bool -> T_FloatVal_56
d_decodeAt_92 v0 v1 v2 v3 v4 v5
  = if coe v4
      then coe
             C_fv'45'fin_58
             (coe
                C__'183'2'94'__18 (coe d_applySign_64 (coe v1) (coe v3))
                (coe d_subExp_76 (coe v0)))
      else (if coe v5
              then coe du_decodeMax_84 (coe v1) (coe v3)
              else coe
                     C_fv'45'fin_58
                     (coe
                        C__'183'2'94'__18
                        (coe
                           d_applySign_64 (coe v1)
                           (coe
                              addInt
                              (coe
                                 MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                                 (coe
                                    MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0)))
                              (coe v3)))
                        (coe d_normExp_70 (coe v0) (coe v2))))
-- Once.Spec.Float.Arith.decode
d_decode_118 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> T_FloatVal_56
d_decode_118 v0 v1
  = coe
      d_decodeAt_92 (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v1)
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe
               addInt
               (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0))
               (coe
                  MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0)))))
      (coe
         MAlonzo.Code.Data.Nat.Base.du__'47'__318
         (coe
            MAlonzo.Code.Once.Spec.Float.Dyadic.d_modPow_54 (coe v1)
            (coe
               addInt
               (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0))
               (coe
                  MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0))))
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe
               MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0))))
      (coe
         MAlonzo.Code.Once.Spec.Float.Dyadic.d_modPow_54 (coe v1)
         (coe
            MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0)))
      (coe
         eqInt
         (coe
            MAlonzo.Code.Data.Nat.Base.du__'47'__318
            (coe
               MAlonzo.Code.Once.Spec.Float.Dyadic.d_modPow_54 (coe v1)
               (coe
                  addInt
                  (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0))
                  (coe
                     MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0))))
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
               (coe
                  MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0))))
         (coe (0 :: Integer)))
      (coe
         eqInt
         (coe
            MAlonzo.Code.Data.Nat.Base.du__'47'__318
            (coe
               MAlonzo.Code.Once.Spec.Float.Dyadic.d_modPow_54 (coe v1)
               (coe
                  addInt
                  (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0))
                  (coe
                     MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0))))
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
               (coe
                  MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0))))
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
            (MAlonzo.Code.Data.Nat.Base.d__'94'__276
               (coe (2 :: Integer))
               (coe
                  MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0)))
            (1 :: Integer)))
-- Once.Spec.Float.Arith.roundMagAt
d_roundMagAt_124 ::
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_roundMagAt_124 v0 v1
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
             (coe (0 :: Integer))
      _ -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Spec.Float.Decimal.du_divRHE_48 (coe v0)
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                   (coe v1)))
             (coe v1)
-- Once.Spec.Float.Arith.roundMag
d_roundMag_132 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_roundMag_132 v0 v1
  = coe
      d_roundMagAt_124 (coe v1)
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (MAlonzo.Code.Once.Spec.Float.Dyadic.d_bitLen_66 (coe v1))
         (addInt
            (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0))))
-- Once.Spec.Float.Arith.roundB
d_roundB_138 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  T_Bin_8 -> Integer
d_roundB_138 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Float.Decimal.d_packAt_160 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Float.Dyadic.d_signBit_70
         (coe d_sigB_14 (coe v1)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_roundMag_132 (coe v0)
            (coe
               MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
               (coe d_sigB_14 (coe v1)))))
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'43'__284
         (coe d_expB_16 (coe v1))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_roundMag_132 (coe v0)
               (coe
                  MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                  (coe d_sigB_14 (coe v1))))))
-- Once.Spec.Float.Arith.xorS
d_xorS_144 :: Integer -> Integer -> Integer
d_xorS_144 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v0) (coe v1)) (coe (0 :: Integer))
      (coe (1 :: Integer))
-- Once.Spec.Float.Arith.negV
d_negV_150 :: T_FloatVal_56 -> T_FloatVal_56
d_negV_150 v0
  = case coe v0 of
      C_fv'45'fin_58 v1 -> coe C_fv'45'fin_58 (coe d_negB_44 (coe v1))
      C_fv'45'inf_60 v1
        -> coe
             C_fv'45'inf_60 (coe d_xorS_144 (coe v1) (coe (1 :: Integer)))
      C_fv'45'nan_62 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Arith.addV
d_addV_156 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  T_FloatVal_56 -> T_FloatVal_56 -> Integer
d_addV_156 v0 v1 v2
  = case coe v1 of
      C_fv'45'fin_58 v3
        -> case coe v2 of
             C_fv'45'fin_58 v4
               -> coe d_roundB_138 (coe v0) (coe d__'43'B__32 (coe v3) (coe v4))
             C_fv'45'inf_60 v4
               -> coe
                    MAlonzo.Code.Once.Spec.Float.Decimal.d_infinity_108 (coe v0)
                    (coe v4)
             C_fv'45'nan_62 -> coe d_nan_80 (coe v0)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fv'45'inf_60 v3
        -> case coe v2 of
             C_fv'45'fin_58 v4
               -> coe
                    MAlonzo.Code.Once.Spec.Float.Decimal.d_infinity_108 (coe v0)
                    (coe v3)
             C_fv'45'inf_60 v4
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe eqInt (coe v3) (coe v4))
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Decimal.d_infinity_108 (coe v0)
                       (coe v3))
                    (coe d_nan_80 (coe v0))
             C_fv'45'nan_62 -> coe d_nan_80 (coe v0)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fv'45'nan_62 -> coe d_nan_80 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Arith.mulV
d_mulV_184 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  T_FloatVal_56 -> T_FloatVal_56 -> Integer
d_mulV_184 v0 v1 v2
  = case coe v1 of
      C_fv'45'fin_58 v3
        -> case coe v2 of
             C_fv'45'fin_58 v4
               -> coe d_roundB_138 (coe v0) (coe d__'42'B__38 (coe v3) (coe v4))
             C_fv'45'inf_60 v4
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe d_isZeroB_48 (coe v3)) (coe d_nan_80 (coe v0))
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Decimal.d_infinity_108 (coe v0)
                       (coe d_xorS_144 (coe d_signB_52 (coe v3)) (coe v4)))
             C_fv'45'nan_62 -> coe d_nan_80 (coe v0)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fv'45'inf_60 v3
        -> case coe v2 of
             C_fv'45'fin_58 v4
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe d_isZeroB_48 (coe v4)) (coe d_nan_80 (coe v0))
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Decimal.d_infinity_108 (coe v0)
                       (coe d_xorS_144 (coe v3) (coe d_signB_52 (coe v4))))
             C_fv'45'inf_60 v4
               -> coe
                    MAlonzo.Code.Once.Spec.Float.Decimal.d_infinity_108 (coe v0)
                    (coe d_xorS_144 (coe v3) (coe v4))
             C_fv'45'nan_62 -> coe d_nan_80 (coe v0)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fv'45'nan_62 -> coe d_nan_80 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Arith.setLow
d_setLow_216 :: Integer -> Integer
d_setLow_216 v0
  = coe
      addInt (coe (1 :: Integer))
      (coe
         mulInt (coe (2 :: Integer))
         (coe
            MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0)
            (coe (2 :: Integer))))
-- Once.Spec.Float.Arith.stickyAt
d_stickyAt_220 :: Integer -> Integer -> Integer
d_stickyAt_220 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v1) (coe (0 :: Integer))) (coe v0)
      (coe d_setLow_216 (coe v0))
-- Once.Spec.Float.Arith.guardShift
d_guardShift_226 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer
d_guardShift_226 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
      (addInt
         (coe
            addInt (coe (3 :: Integer))
            (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_bitLen_66 (coe v2)))
         (coe
            MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0)))
      (MAlonzo.Code.Once.Spec.Float.Dyadic.d_bitLen_66 (coe v1))
-- Once.Spec.Float.Arith.stickyQuot
d_stickyQuot_234 :: Integer -> Integer -> Integer
d_stickyQuot_234 v0 v1
  = coe
      d_stickyAt_220
      (coe
         MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0)
         (coe addInt (coe (1 :: Integer)) (coe v1)))
      (coe
         MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v0)
         (coe addInt (coe (1 :: Integer)) (coe v1)))
-- Once.Spec.Float.Arith.divBin
d_divBin_240 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  T_Bin_8 -> Integer -> Integer -> Integer -> T_Bin_8
d_divBin_240 v0 v1 v2 v3 v4
  = coe
      C__'183'2'94'__18
      (coe
         d_applySign_64 (coe d_xorS_144 (coe d_signB_52 (coe v1)) (coe v2))
         (coe
            d_stickyQuot_234
            (coe
               mulInt
               (coe
                  MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                  (coe d_sigB_14 (coe v1)))
               (coe
                  MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                  (coe
                     d_guardShift_226 (coe v0)
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                        (coe d_sigB_14 (coe v1)))
                     (coe addInt (coe (1 :: Integer)) (coe v4)))))
            (coe v4)))
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'45'__302
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'45'__302
            (coe d_expB_16 (coe v1)) (coe v3))
         (coe
            d_guardShift_226 (coe v0)
            (coe
               MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
               (coe d_sigB_14 (coe v1)))
            (coe addInt (coe (1 :: Integer)) (coe v4))))
-- Once.Spec.Float.Arith.divV
d_divV_252 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  T_FloatVal_56 -> T_FloatVal_56 -> Integer
d_divV_252 v0 v1 v2
  = case coe v1 of
      C_fv'45'fin_58 v3
        -> case coe v2 of
             C_fv'45'fin_58 v4
               -> let v5
                        = MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                            (coe d_sigB_14 (coe v3)) in
                  coe
                    (let v6
                           = MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                               (coe d_sigB_14 (coe v4)) in
                     coe
                       (case coe v5 of
                          0 -> case coe v6 of
                                 0 -> coe d_nan_80 (coe v0)
                                 _ -> coe
                                        MAlonzo.Code.Once.Spec.Float.Decimal.d_signedZero_114
                                        (coe v0)
                                        (coe
                                           d_xorS_144 (coe d_signB_52 (coe v3))
                                           (coe d_signB_52 (coe v4)))
                          _ -> case coe v6 of
                                 0 -> coe
                                        MAlonzo.Code.Once.Spec.Float.Decimal.d_infinity_108 (coe v0)
                                        (coe
                                           d_xorS_144 (coe d_signB_52 (coe v3))
                                           (coe d_signB_52 (coe v4)))
                                 _ -> let v7 = subInt (coe v6) (coe (1 :: Integer)) in
                                      coe
                                        (coe
                                           d_roundB_138 (coe v0)
                                           (coe
                                              d_divBin_240 (coe v0) (coe v3)
                                              (coe d_signB_52 (coe v4)) (coe d_expB_16 (coe v4))
                                              (coe v7)))))
             C_fv'45'inf_60 v4
               -> coe
                    MAlonzo.Code.Once.Spec.Float.Decimal.d_signedZero_114 (coe v0)
                    (coe d_xorS_144 (coe d_signB_52 (coe v3)) (coe v4))
             C_fv'45'nan_62 -> coe d_nan_80 (coe v0)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fv'45'inf_60 v3
        -> case coe v2 of
             C_fv'45'fin_58 v4
               -> coe
                    MAlonzo.Code.Once.Spec.Float.Decimal.d_infinity_108 (coe v0)
                    (coe d_xorS_144 (coe v3) (coe d_signB_52 (coe v4)))
             C_fv'45'inf_60 v4 -> coe d_nan_80 (coe v0)
             C_fv'45'nan_62 -> coe d_nan_80 (coe v0)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fv'45'nan_62 -> coe d_nan_80 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Float.Arith.fadd
d_fadd_316 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer
d_fadd_316 v0 v1 v2
  = coe
      d_addV_156 (coe v0) (coe d_decode_118 (coe v0) (coe v1))
      (coe d_decode_118 (coe v0) (coe v2))
-- Once.Spec.Float.Arith.fsub
d_fsub_318 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer
d_fsub_318 v0 v1 v2
  = coe
      d_addV_156 (coe v0) (coe d_decode_118 (coe v0) (coe v1))
      (coe d_negV_150 (coe d_decode_118 (coe v0) (coe v2)))
-- Once.Spec.Float.Arith.fmul
d_fmul_320 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer
d_fmul_320 v0 v1 v2
  = coe
      d_mulV_184 (coe v0) (coe d_decode_118 (coe v0) (coe v1))
      (coe d_decode_118 (coe v0) (coe v2))
-- Once.Spec.Float.Arith.fdiv
d_fdiv_322 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer
d_fdiv_322 v0 v1 v2
  = coe
      d_divV_252 (coe v0) (coe d_decode_118 (coe v0) (coe v1))
      (coe d_decode_118 (coe v0) (coe v2))
-- Once.Spec.Float.Arith.fnegAt
d_fnegAt_348 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Bool -> Integer
d_fnegAt_348 v0 v1 v2
  = if coe v2
      then coe
             MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1
             (MAlonzo.Code.Data.Nat.Base.d__'94'__276
                (coe (2 :: Integer))
                (coe
                   addInt
                   (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0))
                   (coe
                      MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0))))
      else coe
             addInt
             (coe
                MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                (coe
                   addInt
                   (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0))
                   (coe
                      MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0))))
             (coe v1)
-- Once.Spec.Float.Arith.fneg
d_fneg_358 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer
d_fneg_358 v0 v1
  = coe
      d_fnegAt_348 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe
               addInt
               (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_exp'45'bits_38 (coe v0))
               (coe
                  MAlonzo.Code.Once.Spec.Float.Dyadic.d_sig'45'bits_36 (coe v0))))
         (coe v1))
-- Once.Spec.Float.Arith.i2f
d_i2f_364 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer
d_i2f_364 v0 v1
  = coe
      d_roundB_138 (coe v0)
      (coe C__'183'2'94'__18 (coe v1) (coe (0 :: Integer)))
