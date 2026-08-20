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

module MAlonzo.Code.Once.Float.Dyadic where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.DivMod
import qualified MAlonzo.Code.Data.Nat.Properties

-- Once.Float.Dyadic.Dyadic
d_Dyadic_6 = ()
data T_Dyadic_6 = C__'47'2'94'__16 Integer Integer
-- Once.Float.Dyadic.Dyadic.sig
d_sig_12 :: T_Dyadic_6 -> Integer
d_sig_12 v0
  = case coe v0 of
      C__'47'2'94'__16 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Float.Dyadic.Dyadic.shift
d_shift_14 :: T_Dyadic_6 -> Integer
d_shift_14 v0
  = case coe v0 of
      C__'47'2'94'__16 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Float.Dyadic.fromℕ
d_fromℕ_18 :: Integer -> T_Dyadic_6
d_fromℕ_18 v0 = coe C__'47'2'94'__16 (coe v0) (coe (0 :: Integer))
-- Once.Float.Dyadic.negate
d_negate_22 :: T_Dyadic_6 -> T_Dyadic_6
d_negate_22 v0
  = case coe v0 of
      C__'47'2'94'__16 v1 v2
        -> coe
             C__'47'2'94'__16
             (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1)) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Float.Dyadic.FloatFormat
d_FloatFormat_28 = ()
data T_FloatFormat_28 = C_mkFormat_38 Integer Integer
-- Once.Float.Dyadic.FloatFormat.sig-bits
d_sig'45'bits_34 :: T_FloatFormat_28 -> Integer
d_sig'45'bits_34 v0
  = case coe v0 of
      C_mkFormat_38 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Float.Dyadic.FloatFormat.exp-bits
d_exp'45'bits_36 :: T_FloatFormat_28 -> Integer
d_exp'45'bits_36 v0
  = case coe v0 of
      C_mkFormat_38 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Float.Dyadic.binary32
d_binary32_40 :: T_FloatFormat_28
d_binary32_40
  = coe C_mkFormat_38 (coe (23 :: Integer)) (coe (8 :: Integer))
-- Once.Float.Dyadic.binary64
d_binary64_42 :: T_FloatFormat_28
d_binary64_42
  = coe C_mkFormat_38 (coe (52 :: Integer)) (coe (11 :: Integer))
-- Once.Float.Dyadic.width
d_width_44 :: T_FloatFormat_28 -> Integer
d_width_44 v0
  = coe
      addInt
      (coe addInt (coe (1 :: Integer)) (coe d_exp'45'bits_36 (coe v0)))
      (coe d_sig'45'bits_34 (coe v0))
-- Once.Float.Dyadic.bias
d_bias_48 :: T_FloatFormat_28 -> Integer
d_bias_48 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
      (MAlonzo.Code.Data.Nat.Base.d__'94'__276
         (coe (2 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
            (d_exp'45'bits_36 (coe v0)) (1 :: Integer)))
      (1 :: Integer)
-- Once.Float.Dyadic.modPow
d_modPow_52 :: Integer -> Integer -> Integer
d_modPow_52 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
         (coe v1))
-- Once.Float.Dyadic.modPow<
d_modPow'60'_62 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_modPow'60'_62 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.DivMod.du_m'37'n'60'n_166 (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
         (coe v1))
-- Once.Float.Dyadic.combine-bound
d_combine'45'bound_76 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_combine'45'bound_76 v0 ~v1 v2 v3 v4 v5
  = du_combine'45'bound_76 v0 v2 v3 v4 v5
du_combine'45'bound_76 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_combine'45'bound_76 v0 v1 v2 v3 v4
  = coe du_lemma_102 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.Float.Dyadic._.step1
d_step1_94 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_step1_94 v0 ~v1 ~v2 v3 ~v4 v5 = du_step1_94 v0 v3 v5
du_step1_94 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_step1_94 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3714
      (coe
         mulInt (coe v0)
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe v1)))
      (coe v2)
-- Once.Float.Dyadic._.step2
d_step2_96 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step2_96 = erased
-- Once.Float.Dyadic._.step3
d_step3_98 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_step3_98 v0 ~v1 v2 v3 v4 ~v5 = du_step3_98 v0 v2 v3 v4
du_step3_98 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_step3_98 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'737''45''8804'_4222
      (MAlonzo.Code.Data.Nat.Base.d__'94'__276
         (coe (2 :: Integer)) (coe v2))
      (addInt (coe (1 :: Integer)) (coe v0))
      (MAlonzo.Code.Data.Nat.Base.d__'94'__276
         (coe (2 :: Integer)) (coe v1))
      v3
-- Once.Float.Dyadic._.step4
d_step4_100 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step4_100 = erased
-- Once.Float.Dyadic._.lemma
d_lemma_102 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lemma_102 v0 ~v1 v2 v3 v4 v5 = du_lemma_102 v0 v2 v3 v4 v5
du_lemma_102 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lemma_102 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
      (coe du_step1_94 (coe v0) (coe v2) (coe v4))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
            (coe
               addInt
               (coe
                  MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                  (coe v2))
               (coe
                  mulInt (coe v0)
                  (coe
                     MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                     (coe v2)))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
            (coe du_step3_98 (coe v0) (coe v1) (coe v2) (coe v3))
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
               (coe
                  mulInt
                  (coe
                     MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                     (coe v1))
                  (coe
                     MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                     (coe v2))))))
-- Once.Float.Dyadic.bitLen-go
d_bitLen'45'go_104 :: Integer -> Integer -> Integer
d_bitLen'45'go_104 v0 v1
  = case coe v0 of
      0 -> coe (0 :: Integer)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe (0 :: Integer)
                _ -> coe
                       addInt (coe (1 :: Integer))
                       (coe
                          d_bitLen'45'go_104 (coe v2)
                          (coe
                             MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v1)
                             (coe (2 :: Integer)))))
-- Once.Float.Dyadic.bitLen
d_bitLen_110 :: Integer -> Integer
d_bitLen_110 v0 = coe d_bitLen'45'go_104 (coe v0) (coe v0)
-- Once.Float.Dyadic.signBit
d_signBit_114 :: Integer -> Integer
d_signBit_114 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) -> coe (0 :: Integer)
      _ -> coe (1 :: Integer)
-- Once.Float.Dyadic.expFieldN
d_expFieldN_116 ::
  T_FloatFormat_28 -> Integer -> Integer -> Integer
d_expFieldN_116 v0 v1 v2
  = coe
      d_modPow_52
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (addInt
            (coe d_bias_48 (coe v0))
            (coe
               MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_bitLen_110 (coe v1))
               (1 :: Integer)))
         v2)
      (coe d_exp'45'bits_36 (coe v0))
-- Once.Float.Dyadic.sigFieldN
d_sigFieldN_124 ::
  T_FloatFormat_28 -> Integer -> Integer -> Integer
d_sigFieldN_124 v0 v1 ~v2 = du_sigFieldN_124 v0 v1
du_sigFieldN_124 :: T_FloatFormat_28 -> Integer -> Integer
du_sigFieldN_124 v0 v1
  = coe
      d_modPow_52
      (coe
         mulInt
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1
            (MAlonzo.Code.Data.Nat.Base.d__'94'__276
               (coe (2 :: Integer))
               (coe
                  MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_bitLen_110 (coe v1))
                  (1 :: Integer))))
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe
               MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
               (d_sig'45'bits_34 (coe v0))
               (coe
                  MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_bitLen_110 (coe v1))
                  (1 :: Integer)))))
      (coe d_sig'45'bits_34 (coe v0))
-- Once.Float.Dyadic.encodeMag
d_encodeMag_130 ::
  T_FloatFormat_28 -> Integer -> Integer -> Integer
d_encodeMag_130 v0 v1 v2
  = case coe v1 of
      0 -> coe (0 :: Integer)
      _ -> coe
             addInt (coe du_sigFieldN_124 (coe v0) (coe v1))
             (coe
                mulInt (coe d_expFieldN_116 (coe v0) (coe v1) (coe v2))
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                   (coe d_sig'45'bits_34 (coe v0))))
-- Once.Float.Dyadic.encode
d_encode_140 :: T_FloatFormat_28 -> T_Dyadic_6 -> Integer
d_encode_140 v0 v1
  = coe
      addInt
      (coe
         d_encodeMag_130 (coe v0)
         (coe
            MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
            (coe d_sig_12 (coe v1)))
         (coe d_shift_14 (coe v1)))
      (coe
         mulInt (coe d_signBit_114 (coe d_sig_12 (coe v1)))
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe
               addInt (coe d_exp'45'bits_36 (coe v0))
               (coe d_sig'45'bits_34 (coe v0)))))
-- Once.Float.Dyadic.encodeMag-fits
d_encodeMag'45'fits_152 ::
  T_FloatFormat_28 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_encodeMag'45'fits_152 v0 v1 v2
  = case coe v1 of
      0 -> coe MAlonzo.Code.Data.Nat.Properties.du_m'94'n'62'0_4482
      _ -> coe
             du_combine'45'bound_76
             (coe
                MAlonzo.Code.Data.Nat.Base.du__'37'__330
                (coe
                   MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                   (addInt
                      (coe d_bias_48 (coe v0))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_bitLen_110 (coe v1))
                         (1 :: Integer)))
                   v2)
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                   (coe d_exp'45'bits_36 (coe v0))))
             (coe d_exp'45'bits_36 (coe v0)) (coe d_sig'45'bits_34 (coe v0))
             (coe
                d_modPow'60'_62
                (coe
                   MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                   (addInt
                      (coe d_bias_48 (coe v0))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_bitLen_110 (coe v1))
                         (1 :: Integer)))
                   v2)
                (coe d_exp'45'bits_36 (coe v0)))
             (coe
                d_modPow'60'_62
                (coe
                   mulInt
                   (coe
                      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1
                      (MAlonzo.Code.Data.Nat.Base.d__'94'__276
                         (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_bitLen_110 (coe v1))
                            (1 :: Integer))))
                   (coe
                      MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                         (d_sig'45'bits_34 (coe v0))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_bitLen_110 (coe v1))
                            (1 :: Integer)))))
                (coe d_sig'45'bits_34 (coe v0)))
-- Once.Float.Dyadic.signBit<
d_signBit'60'_166 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_signBit'60'_166 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      _ -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- Once.Float.Dyadic.encode-fits
d_encode'45'fits_172 ::
  T_FloatFormat_28 ->
  T_Dyadic_6 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_encode'45'fits_172 v0 v1
  = coe
      du_combine'45'bound_76 (coe d_signBit_114 (coe d_sig_12 (coe v1)))
      (coe (1 :: Integer))
      (coe
         addInt (coe d_exp'45'bits_36 (coe v0))
         (coe d_sig'45'bits_34 (coe v0)))
      (coe d_signBit'60'_166 (coe d_sig_12 (coe v1)))
      (coe
         d_encodeMag'45'fits_152 (coe v0)
         (coe
            MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
            (coe d_sig_12 (coe v1)))
         (coe d_shift_14 (coe v1)))
