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

module MAlonzo.Code.Once.Word where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sign.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Word.Carrier
d_Carrier_4 :: ()
d_Carrier_4 = erased
-- Once.Word.Width.modulus
d_modulus_10 :: Integer -> Integer
d_modulus_10 v0
  = coe
      MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
      (coe v0)
-- Once.Word.Width.modulus≢0
d_modulus'8802'0_12 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_12 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'94'n'8802'0_4470
      (coe (2 :: Integer)) (coe v0)
-- Once.Word.Width.Word
d_Word_14 :: Integer -> ()
d_Word_14 = erased
-- Once.Word.Width.norm
d_norm_16 :: Integer -> Integer -> Integer
d_norm_16 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v1)
      (coe d_modulus_10 (coe v0))
-- Once.Word.Width.fromℤ
d_fromℤ_20 :: Integer -> Integer -> Integer
d_fromℤ_20 v0 v1
  = case coe v1 of
      _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
          coe d_norm_16 (coe v0) (coe v1)
      _ -> coe
             d_norm_16 (coe v0)
             (coe
                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_modulus_10 (coe v0))
                (d_norm_16 (coe v0) (coe subInt (coe (0 :: Integer)) (coe v1))))
-- Once.Word.Width._⊕_
d__'8853'__26 :: Integer -> Integer -> Integer -> Integer
d__'8853'__26 v0 v1 v2
  = coe d_norm_16 (coe v0) (coe addInt (coe v1) (coe v2))
-- Once.Word.Width._⊖_
d__'8854'__32 :: Integer -> Integer -> Integer -> Integer
d__'8854'__32 v0 v1 v2
  = coe
      d_norm_16 (coe v0)
      (coe
         addInt
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_modulus_10 (coe v0))
            v2)
         (coe v1))
-- Once.Word.Width._⊗_
d__'8855'__38 :: Integer -> Integer -> Integer -> Integer
d__'8855'__38 v0 v1 v2
  = coe d_norm_16 (coe v0) (coe mulInt (coe v1) (coe v2))
-- Once.Word.Width.⊝_
d_'8861'__44 :: Integer -> Integer -> Integer
d_'8861'__44 v0 v1
  = coe
      d_norm_16 (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_modulus_10 (coe v0))
         v1)
-- Once.Word.Width.half
d_half_48 :: Integer -> Integer
d_half_48 v0
  = coe
      MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
      (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 (1 :: Integer))
-- Once.Word.Width.toℤ
d_toℤ_50 :: Integer -> Integer -> Integer
d_toℤ_50 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe ltInt (coe v1) (coe d_half_48 (coe v0))) (coe v1)
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v1)
         (coe d_modulus_10 (coe v0)))
-- Once.Word.Width.intMin
d_intMin_54 :: Integer -> Integer
d_intMin_54 v0 = coe d_half_48 (coe v0)
-- Once.Word.Width.negOne
d_negOne_56 :: Integer -> Integer
d_negOne_56 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_modulus_10 (coe v0))
      (1 :: Integer)
-- Once.Word.Width._<ˢ_
d__'60''738'__58 :: Integer -> Integer -> Integer -> Bool
d__'60''738'__58 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
      (coe
         MAlonzo.Code.Data.Integer.Properties.d__'60''63'__3190
         (coe d_toℤ_50 (coe v0) (coe v1)) (coe d_toℤ_50 (coe v0) (coe v2)))
-- Once.Word.Width._≡ʷ_
d__'8801''695'__64 :: Integer -> Integer -> Integer -> Bool
d__'8801''695'__64 ~v0 v1 v2 = du__'8801''695'__64 v1 v2
du__'8801''695'__64 :: Integer -> Integer -> Bool
du__'8801''695'__64 v0 v1 = coe eqInt (coe v0) (coe v1)
-- Once.Word.Width._divℕ_
d__divℕ__70 :: Integer -> Integer -> Integer -> Integer
d__divℕ__70 ~v0 v1 v2 = du__divℕ__70 v1 v2
du__divℕ__70 :: Integer -> Integer -> Integer
du__divℕ__70 v0 v1
  = case coe v1 of
      0 -> coe (0 :: Integer)
      _ -> coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1)
-- Once.Word.Width._modℕ_
d__modℕ__72 :: Integer -> Integer -> Integer -> Integer
d__modℕ__72 ~v0 v1 v2 = du__modℕ__72 v1 v2
du__modℕ__72 :: Integer -> Integer -> Integer
du__modℕ__72 v0 v1
  = case coe v1 of
      0 -> coe v0
      _ -> coe MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v0) (coe v1)
-- Once.Word.Width.tdivℤ
d_tdivℤ_86 :: Integer -> Integer -> Integer -> Integer
d_tdivℤ_86 ~v0 v1 v2 = du_tdivℤ_86 v1 v2
du_tdivℤ_86 :: Integer -> Integer -> Integer
du_tdivℤ_86 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'9667'__238
      (coe
         MAlonzo.Code.Data.Sign.Base.d__'42'__14
         (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v0))
         (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v1)))
      (coe
         du__divℕ__70
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
-- Once.Word.Width.tmodℤ
d_tmodℤ_88 :: Integer -> Integer -> Integer -> Integer
d_tmodℤ_88 ~v0 v1 v2 = du_tmodℤ_88 v1 v2
du_tmodℤ_88 :: Integer -> Integer -> Integer
du_tmodℤ_88 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'9667'__238
      (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v0))
      (coe
         du__modℕ__72
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
-- Once.Word.Width._/ˢ_
d__'47''738'__98 :: Integer -> Integer -> Integer -> Integer
d__'47''738'__98 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v2) (coe (0 :: Integer)))
      (coe d_negOne_56 (coe v0))
      (coe
         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8743'__24
            (coe eqInt (coe v1) (coe d_intMin_54 (coe v0)))
            (coe eqInt (coe v2) (coe d_negOne_56 (coe v0))))
         (coe d_intMin_54 (coe v0))
         (coe
            d_fromℤ_20 (coe v0)
            (coe
               du_tdivℤ_86 (coe d_toℤ_50 (coe v0) (coe v1))
               (coe d_toℤ_50 (coe v0) (coe v2)))))
-- Once.Word.Width._%ˢ_
d__'37''738'__104 :: Integer -> Integer -> Integer -> Integer
d__'37''738'__104 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v2) (coe (0 :: Integer))) (coe v1)
      (coe
         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8743'__24
            (coe eqInt (coe v1) (coe d_intMin_54 (coe v0)))
            (coe eqInt (coe v2) (coe d_negOne_56 (coe v0))))
         (coe (0 :: Integer))
         (coe
            d_fromℤ_20 (coe v0)
            (coe
               du_tmodℤ_88 (coe d_toℤ_50 (coe v0) (coe v1))
               (coe d_toℤ_50 (coe v0) (coe v2)))))
-- Once.Word.Word64._%ˢ_
d__'37''738'__112 :: Integer -> Integer -> Integer
d__'37''738'__112 = coe d__'37''738'__104 (coe (64 :: Integer))
-- Once.Word.Word64._/ˢ_
d__'47''738'__114 :: Integer -> Integer -> Integer
d__'47''738'__114 = coe d__'47''738'__98 (coe (64 :: Integer))
-- Once.Word.Word64._<ˢ_
d__'60''738'__116 :: Integer -> Integer -> Bool
d__'60''738'__116 = coe d__'60''738'__58 (coe (64 :: Integer))
-- Once.Word.Word64._≡ʷ_
d__'8801''695'__118 :: Integer -> Integer -> Bool
d__'8801''695'__118 = coe du__'8801''695'__64
-- Once.Word.Word64._⊕_
d__'8853'__120 :: Integer -> Integer -> Integer
d__'8853'__120 = coe d__'8853'__26 (coe (64 :: Integer))
-- Once.Word.Word64._⊖_
d__'8854'__122 :: Integer -> Integer -> Integer
d__'8854'__122 = coe d__'8854'__32 (coe (64 :: Integer))
-- Once.Word.Word64._⊗_
d__'8855'__124 :: Integer -> Integer -> Integer
d__'8855'__124 = coe d__'8855'__38 (coe (64 :: Integer))
-- Once.Word.Word64.Word
d_Word_126 :: ()
d_Word_126 = erased
-- Once.Word.Word64.fromℤ
d_fromℤ_128 :: Integer -> Integer
d_fromℤ_128 = coe d_fromℤ_20 (coe (64 :: Integer))
-- Once.Word.Word64.half
d_half_130 :: Integer
d_half_130 = coe d_half_48 (coe (64 :: Integer))
-- Once.Word.Word64.intMin
d_intMin_132 :: Integer
d_intMin_132 = coe d_intMin_54 (coe (64 :: Integer))
-- Once.Word.Word64.modulus
d_modulus_134 :: Integer
d_modulus_134 = coe d_modulus_10 (coe (64 :: Integer))
-- Once.Word.Word64.modulus≢0
d_modulus'8802'0_136 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_136
  = coe d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.Word.Word64.negOne
d_negOne_138 :: Integer
d_negOne_138 = coe d_negOne_56 (coe (64 :: Integer))
-- Once.Word.Word64.norm
d_norm_140 :: Integer -> Integer
d_norm_140 = coe d_norm_16 (coe (64 :: Integer))
-- Once.Word.Word64.toℤ
d_toℤ_142 :: Integer -> Integer
d_toℤ_142 = coe d_toℤ_50 (coe (64 :: Integer))
-- Once.Word.Word64.⊝_
d_'8861'__144 :: Integer -> Integer
d_'8861'__144 = coe d_'8861'__44 (coe (64 :: Integer))
