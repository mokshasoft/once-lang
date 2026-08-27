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

module MAlonzo.Code.Once.Float.Arith where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Float.Dyadic

-- Once.Float.Arith.Bin
d_Bin_6 = ()
data T_Bin_6 = C__'183'2'94'__16 Integer Integer
-- Once.Float.Arith.Bin.sigB
d_sigB_12 :: T_Bin_6 -> Integer
d_sigB_12 v0
  = case coe v0 of
      C__'183'2'94'__16 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Float.Arith.Bin.expB
d_expB_14 :: T_Bin_6 -> Integer
d_expB_14 v0
  = case coe v0 of
      C__'183'2'94'__16 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Float.Arith.addAt
d_addAt_18 ::
  Integer -> Integer -> Integer -> Integer -> Integer -> T_Bin_6
d_addAt_18 v0 v1 v2 v3 v4
  = coe
      C__'183'2'94'__16
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
-- Once.Float.Arith._+B_
d__'43'B__30 :: T_Bin_6 -> T_Bin_6 -> T_Bin_6
d__'43'B__30 v0 v1
  = coe
      d_addAt_18 (coe d_sigB_12 (coe v0)) (coe d_expB_14 (coe v0))
      (coe d_sigB_12 (coe v1)) (coe d_expB_14 (coe v1))
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'8851'__348
         (coe d_expB_14 (coe v0)) (coe d_expB_14 (coe v1)))
-- Once.Float.Arith._*B_
d__'42'B__36 :: T_Bin_6 -> T_Bin_6 -> T_Bin_6
d__'42'B__36 v0 v1
  = coe
      C__'183'2'94'__16
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'42'__316
         (coe d_sigB_12 (coe v0)) (coe d_sigB_12 (coe v1)))
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'43'__284
         (coe d_expB_14 (coe v0)) (coe d_expB_14 (coe v1)))
-- Once.Float.Arith.negB
d_negB_42 :: T_Bin_6 -> T_Bin_6
d_negB_42 v0
  = coe
      C__'183'2'94'__16
      (coe
         MAlonzo.Code.Data.Integer.Base.d_'45'__260
         (coe d_sigB_12 (coe v0)))
      (coe d_expB_14 (coe v0))
-- Once.Float.Arith.isZeroB
d_isZeroB_46 :: T_Bin_6 -> Bool
d_isZeroB_46 v0
  = coe
      eqInt
      (coe
         MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
         (coe d_sigB_12 (coe v0)))
      (coe (0 :: Integer))
-- Once.Float.Arith.signB
d_signB_50 :: T_Bin_6 -> Integer
d_signB_50 v0
  = coe
      MAlonzo.Code.Once.Float.Dyadic.d_signBit_114
      (coe d_sigB_12 (coe v0))
-- Once.Float.Arith.FloatVal
d_FloatVal_54 = ()
data T_FloatVal_54
  = C_fv'45'fin_56 T_Bin_6 | C_fv'45'inf_58 Integer | C_fv'45'nan_60
-- Once.Float.Arith.applySign
d_applySign_62 :: Integer -> Integer -> Integer
d_applySign_62 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v0) (coe (0 :: Integer))) (coe v1)
      (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1))
-- Once.Float.Arith.normExp
d_normExp_68 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer
d_normExp_68 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v1)
      (coe
         addInt (coe MAlonzo.Code.Once.Float.Dyadic.d_bias_48 (coe v0))
         (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0)))
-- Once.Float.Arith.subExp
d_subExp_74 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 -> Integer
d_subExp_74 v0
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe (1 :: Integer))
      (coe
         addInt (coe MAlonzo.Code.Once.Float.Dyadic.d_bias_48 (coe v0))
         (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0)))
-- Once.Float.Arith.nan
d_nan_78 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 -> Integer
d_nan_78 v0
  = coe
      addInt
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
            (MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0))
            (1 :: Integer)))
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
-- Once.Float.Arith.decodeMax
d_decodeMax_82 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer -> T_FloatVal_54
d_decodeMax_82 ~v0 v1 v2 = du_decodeMax_82 v1 v2
du_decodeMax_82 :: Integer -> Integer -> T_FloatVal_54
du_decodeMax_82 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v1) (coe (0 :: Integer)))
      (coe C_fv'45'inf_58 (coe v0)) (coe C_fv'45'nan_60)
-- Once.Float.Arith.decodeAt
d_decodeAt_90 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer -> Integer -> Bool -> Bool -> T_FloatVal_54
d_decodeAt_90 v0 v1 v2 v3 v4 v5
  = if coe v4
      then coe
             C_fv'45'fin_56
             (coe
                C__'183'2'94'__16 (coe d_applySign_62 (coe v1) (coe v3))
                (coe d_subExp_74 (coe v0)))
      else (if coe v5
              then coe du_decodeMax_82 (coe v1) (coe v3)
              else coe
                     C_fv'45'fin_56
                     (coe
                        C__'183'2'94'__16
                        (coe
                           d_applySign_62 (coe v1)
                           (coe
                              addInt
                              (coe
                                 MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                                 (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0)))
                              (coe v3)))
                        (coe d_normExp_68 (coe v0) (coe v2))))
-- Once.Float.Arith.decode
d_decode_116 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> T_FloatVal_54
d_decode_116 v0 v1
  = coe
      d_decodeAt_90 (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v1)
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe
               addInt
               (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0))
               (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0)))))
      (coe
         MAlonzo.Code.Data.Nat.Base.du__'47'__318
         (coe
            MAlonzo.Code.Once.Float.Dyadic.d_modPow_52 (coe v1)
            (coe
               addInt
               (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0))
               (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0))))
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0))))
      (coe
         MAlonzo.Code.Once.Float.Dyadic.d_modPow_52 (coe v1)
         (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0)))
      (coe
         eqInt
         (coe
            MAlonzo.Code.Data.Nat.Base.du__'47'__318
            (coe
               MAlonzo.Code.Once.Float.Dyadic.d_modPow_52 (coe v1)
               (coe
                  addInt
                  (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0))
                  (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0))))
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
               (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0))))
         (coe (0 :: Integer)))
      (coe
         eqInt
         (coe
            MAlonzo.Code.Data.Nat.Base.du__'47'__318
            (coe
               MAlonzo.Code.Once.Float.Dyadic.d_modPow_52 (coe v1)
               (coe
                  addInt
                  (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0))
                  (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0))))
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
               (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0))))
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
            (MAlonzo.Code.Data.Nat.Base.d__'94'__276
               (coe (2 :: Integer))
               (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0)))
            (1 :: Integer)))
-- Once.Float.Arith.roundMagAt
d_roundMagAt_122 ::
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_roundMagAt_122 v0 v1
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
             (coe (0 :: Integer))
      _ -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Float.Decimal.du_divRHE_46 (coe v0)
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                   (coe v1)))
             (coe v1)
-- Once.Float.Arith.roundMag
d_roundMag_130 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_roundMag_130 v0 v1
  = coe
      d_roundMagAt_122 (coe v1)
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (MAlonzo.Code.Once.Float.Dyadic.d_bitLen_110 (coe v1))
         (addInt
            (coe (1 :: Integer))
            (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0))))
-- Once.Float.Arith.roundB
d_roundB_136 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  T_Bin_6 -> Integer
d_roundB_136 v0 v1
  = coe
      MAlonzo.Code.Once.Float.Decimal.d_packAt_158 (coe v0)
      (coe
         MAlonzo.Code.Once.Float.Dyadic.d_signBit_114
         (coe d_sigB_12 (coe v1)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_roundMag_130 (coe v0)
            (coe
               MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
               (coe d_sigB_12 (coe v1)))))
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'43'__284
         (coe d_expB_14 (coe v1))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_roundMag_130 (coe v0)
               (coe
                  MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                  (coe d_sigB_12 (coe v1))))))
-- Once.Float.Arith.xorS
d_xorS_142 :: Integer -> Integer -> Integer
d_xorS_142 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v0) (coe v1)) (coe (0 :: Integer))
      (coe (1 :: Integer))
-- Once.Float.Arith.negV
d_negV_148 :: T_FloatVal_54 -> T_FloatVal_54
d_negV_148 v0
  = case coe v0 of
      C_fv'45'fin_56 v1 -> coe C_fv'45'fin_56 (coe d_negB_42 (coe v1))
      C_fv'45'inf_58 v1
        -> coe
             C_fv'45'inf_58 (coe d_xorS_142 (coe v1) (coe (1 :: Integer)))
      C_fv'45'nan_60 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Float.Arith.addV
d_addV_154 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  T_FloatVal_54 -> T_FloatVal_54 -> Integer
d_addV_154 v0 v1 v2
  = case coe v1 of
      C_fv'45'fin_56 v3
        -> case coe v2 of
             C_fv'45'fin_56 v4
               -> coe d_roundB_136 (coe v0) (coe d__'43'B__30 (coe v3) (coe v4))
             C_fv'45'inf_58 v4
               -> coe
                    MAlonzo.Code.Once.Float.Decimal.d_infinity_106 (coe v0) (coe v4)
             C_fv'45'nan_60 -> coe d_nan_78 (coe v0)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fv'45'inf_58 v3
        -> case coe v2 of
             C_fv'45'fin_56 v4
               -> coe
                    MAlonzo.Code.Once.Float.Decimal.d_infinity_106 (coe v0) (coe v3)
             C_fv'45'inf_58 v4
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe eqInt (coe v3) (coe v4))
                    (coe
                       MAlonzo.Code.Once.Float.Decimal.d_infinity_106 (coe v0) (coe v3))
                    (coe d_nan_78 (coe v0))
             C_fv'45'nan_60 -> coe d_nan_78 (coe v0)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fv'45'nan_60 -> coe d_nan_78 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Float.Arith.mulV
d_mulV_182 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  T_FloatVal_54 -> T_FloatVal_54 -> Integer
d_mulV_182 v0 v1 v2
  = case coe v1 of
      C_fv'45'fin_56 v3
        -> case coe v2 of
             C_fv'45'fin_56 v4
               -> coe d_roundB_136 (coe v0) (coe d__'42'B__36 (coe v3) (coe v4))
             C_fv'45'inf_58 v4
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe d_isZeroB_46 (coe v3)) (coe d_nan_78 (coe v0))
                    (coe
                       MAlonzo.Code.Once.Float.Decimal.d_infinity_106 (coe v0)
                       (coe d_xorS_142 (coe d_signB_50 (coe v3)) (coe v4)))
             C_fv'45'nan_60 -> coe d_nan_78 (coe v0)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fv'45'inf_58 v3
        -> case coe v2 of
             C_fv'45'fin_56 v4
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe d_isZeroB_46 (coe v4)) (coe d_nan_78 (coe v0))
                    (coe
                       MAlonzo.Code.Once.Float.Decimal.d_infinity_106 (coe v0)
                       (coe d_xorS_142 (coe v3) (coe d_signB_50 (coe v4))))
             C_fv'45'inf_58 v4
               -> coe
                    MAlonzo.Code.Once.Float.Decimal.d_infinity_106 (coe v0)
                    (coe d_xorS_142 (coe v3) (coe v4))
             C_fv'45'nan_60 -> coe d_nan_78 (coe v0)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fv'45'nan_60 -> coe d_nan_78 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Float.Arith.fadd
d_fadd_214 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer -> Integer
d_fadd_214 v0 v1 v2
  = coe
      d_addV_154 (coe v0) (coe d_decode_116 (coe v0) (coe v1))
      (coe d_decode_116 (coe v0) (coe v2))
-- Once.Float.Arith.fsub
d_fsub_216 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer -> Integer
d_fsub_216 v0 v1 v2
  = coe
      d_addV_154 (coe v0) (coe d_decode_116 (coe v0) (coe v1))
      (coe d_negV_148 (coe d_decode_116 (coe v0) (coe v2)))
-- Once.Float.Arith.fmul
d_fmul_218 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer -> Integer
d_fmul_218 v0 v1 v2
  = coe
      d_mulV_182 (coe v0) (coe d_decode_116 (coe v0) (coe v1))
      (coe d_decode_116 (coe v0) (coe v2))
-- Once.Float.Arith.fnegAt
d_fnegAt_238 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Bool -> Integer
d_fnegAt_238 v0 v1 v2
  = if coe v2
      then coe
             MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1
             (MAlonzo.Code.Data.Nat.Base.d__'94'__276
                (coe (2 :: Integer))
                (coe
                   addInt
                   (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0))
                   (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0))))
      else coe
             addInt
             (coe
                MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                (coe
                   addInt
                   (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0))
                   (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0))))
             (coe v1)
-- Once.Float.Arith.fneg
d_fneg_248 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer
d_fneg_248 v0 v1
  = coe
      d_fnegAt_238 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe
               addInt
               (coe MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_36 (coe v0))
               (coe MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_34 (coe v0))))
         (coe v1))
-- Once.Float.Arith.i2f
d_i2f_254 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer
d_i2f_254 v0 v1
  = coe
      d_roundB_136 (coe v0)
      (coe C__'183'2'94'__16 (coe v1) (coe (0 :: Integer)))
-- Once.Float.Arith.≡ᵇ-sym
d_'8801''7495''45'sym_316 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'sym_316 = erased
-- Once.Float.Arith.≡ᵇ⇒≡
d_'8801''7495''8658''8801'_326 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''8658''8801'_326 = erased
-- Once.Float.Arith.+B-comm
d_'43'B'45'comm_338 ::
  T_Bin_6 ->
  T_Bin_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43'B'45'comm_338 = erased
-- Once.Float.Arith.*B-comm
d_'42'B'45'comm_358 ::
  T_Bin_6 ->
  T_Bin_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42'B'45'comm_358 = erased
-- Once.Float.Arith.addV-inf-aux
d_addV'45'inf'45'aux_376 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  Integer ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_addV'45'inf'45'aux_376 = erased
-- Once.Float.Arith.addV-comm
d_addV'45'comm_398 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  T_FloatVal_54 ->
  T_FloatVal_54 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_addV'45'comm_398 = erased
-- Once.Float.Arith.xorS-comm
d_xorS'45'comm_438 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xorS'45'comm_438 = erased
-- Once.Float.Arith.mulV-inf-fin-aux
d_mulV'45'inf'45'fin'45'aux_456 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  Integer -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mulV'45'inf'45'fin'45'aux_456 = erased
-- Once.Float.Arith.mulV-comm
d_mulV'45'comm_476 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  T_FloatVal_54 ->
  T_FloatVal_54 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mulV'45'comm_476 = erased
-- Once.Float.Arith.fadd-comm
d_fadd'45'comm_518 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fadd'45'comm_518 = erased
-- Once.Float.Arith.fmul-comm
d_fmul'45'comm_532 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmul'45'comm_532 = erased
