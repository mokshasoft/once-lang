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

module MAlonzo.Code.Once.Spec.Word where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sign.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Spec.Word.Carrier
d_Carrier_6 :: ()
d_Carrier_6 = erased
-- Once.Spec.Word.Width.modulus
d_modulus_12 :: Integer -> Integer
d_modulus_12 v0
  = coe
      MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
      (coe v0)
-- Once.Spec.Word.Width.modulus≢0
d_modulus'8802'0_14 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_14 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'94'n'8802'0_4470
      (coe (2 :: Integer)) (coe v0)
-- Once.Spec.Word.Width.Word
d_Word_16 :: Integer -> ()
d_Word_16 = erased
-- Once.Spec.Word.Width.norm
d_norm_18 :: Integer -> Integer -> Integer
d_norm_18 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v1)
      (coe d_modulus_12 (coe v0))
-- Once.Spec.Word.Width.fromℤ
d_fromℤ_22 :: Integer -> Integer -> Integer
d_fromℤ_22 v0 v1
  = case coe v1 of
      _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
          coe d_norm_18 (coe v0) (coe v1)
      _ -> coe
             d_norm_18 (coe v0)
             (coe
                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_modulus_12 (coe v0))
                (d_norm_18 (coe v0) (coe subInt (coe (0 :: Integer)) (coe v1))))
-- Once.Spec.Word.Width._⊕_
d__'8853'__28 :: Integer -> Integer -> Integer -> Integer
d__'8853'__28 v0 v1 v2
  = coe d_norm_18 (coe v0) (coe addInt (coe v1) (coe v2))
-- Once.Spec.Word.Width._⊖_
d__'8854'__34 :: Integer -> Integer -> Integer -> Integer
d__'8854'__34 v0 v1 v2
  = coe
      d_norm_18 (coe v0)
      (coe
         addInt
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_modulus_12 (coe v0))
            v2)
         (coe v1))
-- Once.Spec.Word.Width._⊗_
d__'8855'__40 :: Integer -> Integer -> Integer -> Integer
d__'8855'__40 v0 v1 v2
  = coe d_norm_18 (coe v0) (coe mulInt (coe v1) (coe v2))
-- Once.Spec.Word.Width.⊝_
d_'8861'__46 :: Integer -> Integer -> Integer
d_'8861'__46 v0 v1
  = coe
      d_norm_18 (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_modulus_12 (coe v0))
         v1)
-- Once.Spec.Word.Width.half
d_half_50 :: Integer -> Integer
d_half_50 v0
  = coe
      MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
      (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 (1 :: Integer))
-- Once.Spec.Word.Width.toℤ
d_toℤ_52 :: Integer -> Integer -> Integer
d_toℤ_52 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe ltInt (coe v1) (coe d_half_50 (coe v0))) (coe v1)
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v1)
         (coe d_modulus_12 (coe v0)))
-- Once.Spec.Word.Width.intMin
d_intMin_56 :: Integer -> Integer
d_intMin_56 v0 = coe d_half_50 (coe v0)
-- Once.Spec.Word.Width.negOne
d_negOne_58 :: Integer -> Integer
d_negOne_58 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_modulus_12 (coe v0))
      (1 :: Integer)
-- Once.Spec.Word.Width.InRange
d_InRange_60 :: Integer -> Integer -> ()
d_InRange_60 = erased
-- Once.Spec.Word.Width.inRange?
d_inRange'63'_66 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_66 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
      (coe
         MAlonzo.Code.Data.Integer.Properties.d__'8804''63'__2880
         (coe
            MAlonzo.Code.Data.Integer.Base.d_'45'__260
            (coe d_half_50 (coe v0)))
         (coe v1))
      (coe
         MAlonzo.Code.Data.Integer.Properties.d__'8804''63'__2880 (coe v1)
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_half_50 (coe v0))
            (1 :: Integer)))
-- Once.Spec.Word.Width.toWord
d_toWord_72 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_72 v0 v1 ~v2 = du_toWord_72 v0 v1
du_toWord_72 :: Integer -> Integer -> Integer
du_toWord_72 v0 v1 = coe d_fromℤ_22 (coe v0) (coe v1)
-- Once.Spec.Word.Width._<ˢ_
d__'60''738'__76 :: Integer -> Integer -> Integer -> Bool
d__'60''738'__76 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
      (coe
         MAlonzo.Code.Data.Integer.Properties.d__'60''63'__3190
         (coe d_toℤ_52 (coe v0) (coe v1)) (coe d_toℤ_52 (coe v0) (coe v2)))
-- Once.Spec.Word.Width._≡ʷ_
d__'8801''695'__82 :: Integer -> Integer -> Integer -> Bool
d__'8801''695'__82 ~v0 v1 v2 = du__'8801''695'__82 v1 v2
du__'8801''695'__82 :: Integer -> Integer -> Bool
du__'8801''695'__82 v0 v1 = coe eqInt (coe v0) (coe v1)
-- Once.Spec.Word.Width._divℕ_
d__divℕ__88 :: Integer -> Integer -> Integer -> Integer
d__divℕ__88 ~v0 v1 v2 = du__divℕ__88 v1 v2
du__divℕ__88 :: Integer -> Integer -> Integer
du__divℕ__88 v0 v1
  = case coe v1 of
      0 -> coe (0 :: Integer)
      _ -> coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1)
-- Once.Spec.Word.Width._modℕ_
d__modℕ__90 :: Integer -> Integer -> Integer -> Integer
d__modℕ__90 ~v0 v1 v2 = du__modℕ__90 v1 v2
du__modℕ__90 :: Integer -> Integer -> Integer
du__modℕ__90 v0 v1
  = case coe v1 of
      0 -> coe v0
      _ -> coe MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v0) (coe v1)
-- Once.Spec.Word.Width.tdivℤ
d_tdivℤ_104 :: Integer -> Integer -> Integer -> Integer
d_tdivℤ_104 ~v0 v1 v2 = du_tdivℤ_104 v1 v2
du_tdivℤ_104 :: Integer -> Integer -> Integer
du_tdivℤ_104 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'9667'__238
      (coe
         MAlonzo.Code.Data.Sign.Base.d__'42'__14
         (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v0))
         (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v1)))
      (coe
         du__divℕ__88
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
-- Once.Spec.Word.Width.tmodℤ
d_tmodℤ_106 :: Integer -> Integer -> Integer -> Integer
d_tmodℤ_106 ~v0 v1 v2 = du_tmodℤ_106 v1 v2
du_tmodℤ_106 :: Integer -> Integer -> Integer
du_tmodℤ_106 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'9667'__238
      (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v0))
      (coe
         du__modℕ__90
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
-- Once.Spec.Word.Width._/ˢ_
d__'47''738'__116 :: Integer -> Integer -> Integer -> Integer
d__'47''738'__116 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v2) (coe (0 :: Integer)))
      (coe d_negOne_58 (coe v0))
      (coe
         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8743'__24
            (coe eqInt (coe v1) (coe d_intMin_56 (coe v0)))
            (coe eqInt (coe v2) (coe d_negOne_58 (coe v0))))
         (coe d_intMin_56 (coe v0))
         (coe
            d_fromℤ_22 (coe v0)
            (coe
               du_tdivℤ_104 (coe d_toℤ_52 (coe v0) (coe v1))
               (coe d_toℤ_52 (coe v0) (coe v2)))))
-- Once.Spec.Word.Width._%ˢ_
d__'37''738'__122 :: Integer -> Integer -> Integer -> Integer
d__'37''738'__122 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v2) (coe (0 :: Integer))) (coe v1)
      (coe
         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8743'__24
            (coe eqInt (coe v1) (coe d_intMin_56 (coe v0)))
            (coe eqInt (coe v2) (coe d_negOne_58 (coe v0))))
         (coe (0 :: Integer))
         (coe
            d_fromℤ_22 (coe v0)
            (coe
               du_tmodℤ_106 (coe d_toℤ_52 (coe v0) (coe v1))
               (coe d_toℤ_52 (coe v0) (coe v2)))))
-- Once.Spec.Word.Word64._%ˢ_
d__'37''738'__130 :: Integer -> Integer -> Integer
d__'37''738'__130 = coe d__'37''738'__122 (coe (64 :: Integer))
-- Once.Spec.Word.Word64._/ˢ_
d__'47''738'__132 :: Integer -> Integer -> Integer
d__'47''738'__132 = coe d__'47''738'__116 (coe (64 :: Integer))
-- Once.Spec.Word.Word64._<ˢ_
d__'60''738'__134 :: Integer -> Integer -> Bool
d__'60''738'__134 = coe d__'60''738'__76 (coe (64 :: Integer))
-- Once.Spec.Word.Word64._divℕ_
d__divℕ__136 :: Integer -> Integer -> Integer
d__divℕ__136 = coe du__divℕ__88
-- Once.Spec.Word.Word64._modℕ_
d__modℕ__138 :: Integer -> Integer -> Integer
d__modℕ__138 = coe du__modℕ__90
-- Once.Spec.Word.Word64._≡ʷ_
d__'8801''695'__140 :: Integer -> Integer -> Bool
d__'8801''695'__140 = coe du__'8801''695'__82
-- Once.Spec.Word.Word64._⊕_
d__'8853'__142 :: Integer -> Integer -> Integer
d__'8853'__142 = coe d__'8853'__28 (coe (64 :: Integer))
-- Once.Spec.Word.Word64._⊖_
d__'8854'__144 :: Integer -> Integer -> Integer
d__'8854'__144 = coe d__'8854'__34 (coe (64 :: Integer))
-- Once.Spec.Word.Word64._⊗_
d__'8855'__146 :: Integer -> Integer -> Integer
d__'8855'__146 = coe d__'8855'__40 (coe (64 :: Integer))
-- Once.Spec.Word.Word64.InRange
d_InRange_148 :: Integer -> ()
d_InRange_148 = erased
-- Once.Spec.Word.Word64.Word
d_Word_150 :: ()
d_Word_150 = erased
-- Once.Spec.Word.Word64.fromℤ
d_fromℤ_152 :: Integer -> Integer
d_fromℤ_152 = coe d_fromℤ_22 (coe (64 :: Integer))
-- Once.Spec.Word.Word64.half
d_half_154 :: Integer
d_half_154 = coe d_half_50 (coe (64 :: Integer))
-- Once.Spec.Word.Word64.inRange?
d_inRange'63'_156 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_156 = coe d_inRange'63'_66 (coe (64 :: Integer))
-- Once.Spec.Word.Word64.intMin
d_intMin_158 :: Integer
d_intMin_158 = coe d_intMin_56 (coe (64 :: Integer))
-- Once.Spec.Word.Word64.modulus
d_modulus_160 :: Integer
d_modulus_160 = coe d_modulus_12 (coe (64 :: Integer))
-- Once.Spec.Word.Word64.modulus≢0
d_modulus'8802'0_162 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_162
  = coe d_modulus'8802'0_14 (coe (64 :: Integer))
-- Once.Spec.Word.Word64.negOne
d_negOne_164 :: Integer
d_negOne_164 = coe d_negOne_58 (coe (64 :: Integer))
-- Once.Spec.Word.Word64.norm
d_norm_166 :: Integer -> Integer
d_norm_166 = coe d_norm_18 (coe (64 :: Integer))
-- Once.Spec.Word.Word64.tdivℤ
d_tdivℤ_168 :: Integer -> Integer -> Integer
d_tdivℤ_168 = coe du_tdivℤ_104
-- Once.Spec.Word.Word64.tmodℤ
d_tmodℤ_170 :: Integer -> Integer -> Integer
d_tmodℤ_170 = coe du_tmodℤ_106
-- Once.Spec.Word.Word64.toWord
d_toWord_172 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_172 v0 v1 = coe du_toWord_72 (coe (64 :: Integer)) v0
-- Once.Spec.Word.Word64.toℤ
d_toℤ_174 :: Integer -> Integer
d_toℤ_174 = coe d_toℤ_52 (coe (64 :: Integer))
-- Once.Spec.Word.Word64.⊝_
d_'8861'__176 :: Integer -> Integer
d_'8861'__176 = coe d_'8861'__46 (coe (64 :: Integer))
