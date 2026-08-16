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
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.DivMod
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
-- Once.Word.Width.shlᵂ
d_shl'7490'_110 :: Integer -> Integer -> Integer -> Integer
d_shl'7490'_110 v0 v1 v2
  = coe
      d_norm_16 (coe v0)
      (coe
         mulInt (coe v1)
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe v2)))
-- Once.Word.Width.sdiv2ᵏ
d_sdiv2'7503'_116 :: Integer -> Integer -> Integer -> Integer
d_sdiv2'7503'_116 v0 v1 v2
  = coe
      d__'47''738'__98 (coe v0) (coe v1)
      (coe
         d_fromℤ_20 (coe v0)
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe v2)))
-- Once.Word.Width.⊗-pow2
d_'8855''45'pow2_126 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_126 = erased
-- Once.Word.Width./ˢ-pow2
d_'47''738''45'pow2_138 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_138 = erased
-- Once.Word.Width.0<modulus
d_0'60'modulus_144 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_144 ~v0 = du_0'60'modulus_144
du_0'60'modulus_144 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'modulus_144
  = coe MAlonzo.Code.Data.Nat.Properties.du_m'94'n'62'0_4482
-- Once.Word.Width.0<half
d_0'60'half_146 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_146 ~v0 = du_0'60'half_146
du_0'60'half_146 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'half_146
  = coe MAlonzo.Code.Data.Nat.Properties.du_m'94'n'62'0_4482
-- Once.Word.Width.fromℤ-0
d_fromℤ'45'0_148 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_148 = erased
-- Once.Word.Width.fromℤ-in-range
d_fromℤ'45'in'45'range_152 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_152 v0 v1
  = case coe v1 of
      _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
          coe
            MAlonzo.Code.Data.Nat.DivMod.du_m'37'n'60'n_166 (coe v1)
            (coe d_modulus_10 (coe v0))
      _ -> coe
             MAlonzo.Code.Data.Nat.DivMod.du_m'37'n'60'n_166
             (coe
                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_modulus_10 (coe v0))
                (d_norm_16 (coe v0) (coe subInt (coe (0 :: Integer)) (coe v1))))
             (coe d_modulus_10 (coe v0))
-- Once.Word.Width./ˢ-zero
d_'47''738''45'zero_160 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_160 = erased
-- Once.Word.Width.%ˢ-zero
d_'37''738''45'zero_166 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_166 = erased
-- Once.Word.Width.≡ᵇ-refl
d_'8801''7495''45'refl_172 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_172 = erased
-- Once.Word.Width.≡ᵇ0-false
d_'8801''7495'0'45'false_178 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_178 = erased
-- Once.Word.Width.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_184 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_184 = erased
-- Once.Word.Width./ˢ-else
d_'47''738''45'else_214 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_214 = erased
-- Once.Word.Width./ˢ-mid
d_'47''738''45'mid_236 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_236 = erased
-- Once.Word.Width.%ˢ-else
d_'37''738''45'else_258 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_258 = erased
-- Once.Word.Width.%ˢ-mid
d_'37''738''45'mid_280 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_280 = erased
-- Once.Word.Width.tdiv-neg1
d_tdiv'45'neg1_300 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_300 = erased
-- Once.Word.Width.tmod-neg1
d_tmod'45'neg1_312 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_312 = erased
-- Once.Word.Width._.half≡2^b
d_half'8801'2'94'b_326 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_326 = erased
-- Once.Word.Width._.2*n≡n+n
d_2'42'n'8801'n'43'n_332 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_332 = erased
-- Once.Word.Width._.mod≡half+half
d_mod'8801'half'43'half_338 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_338 = erased
-- Once.Word.Width._.2≤modulus
d_2'8804'modulus_344 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_344 v0 ~v1 ~v2 = du_2'8804'modulus_344 v0
du_2'8804'modulus_344 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_2'8804'modulus_344 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'45''8804'_3672
      (coe d_half_48 (coe v0)) (coe du_0'60'half_146)
      (coe du_0'60'half_146)
-- Once.Word.Width._.0<negOne
d_0'60'negOne_348 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_348 v0 ~v1 ~v2 = du_0'60'negOne_348 v0
du_0'60'negOne_348 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'negOne_348 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'737''45''8804'_5232
      (coe (2 :: Integer)) (coe d_modulus_10 (coe v0))
      (coe (1 :: Integer)) (coe du_2'8804'modulus_344 (coe v0))
-- Once.Word.Width._.negOne≢0
d_negOne'8802'0_350 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_350 = erased
-- Once.Word.Width._.half<modulus
d_half'60'modulus_352 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_352 v0 ~v1 ~v2 = du_half'60'modulus_352 v0
du_half'60'modulus_352 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_half'60'modulus_352 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3714
      (coe d_half_48 (coe v0)) (coe du_0'60'half_146)
-- Once.Word.Width._.sucNegOne≡mod
d_sucNegOne'8801'mod_358 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_358 = erased
-- Once.Word.Width._.negOne<modulus
d_negOne'60'modulus_360 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_360 v0 ~v1 ~v2 = du_negOne'60'modulus_360 v0
du_negOne'60'modulus_360 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_negOne'60'modulus_360 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (1 :: Integer)) (coe d_negOne_56 (coe v0)))
-- Once.Word.Width._.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_364 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_364 = erased
-- Once.Word.Width._.mod∸half≡half
d_mod'8760'half'8801'half_366 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_366 = erased
-- Once.Word.Width._.⊝-intMin
d_'8861''45'intMin_370 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_370 = erased
-- Once.Word.Width._.half≤negOne
d_half'8804'negOne_372 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_372 v0 ~v1 ~v2 = du_half'8804'negOne_372 v0
du_half'8804'negOne_372 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_half'8804'negOne_372 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'737''45''8804'_5232
      (coe addInt (coe (1 :: Integer)) (coe d_half_48 (coe v0)))
      (coe addInt (coe d_half_48 (coe v0)) (coe d_half_48 (coe v0)))
      (coe (1 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         (d_half_48 (coe v0)) (1 :: Integer) (d_half_48 (coe v0))
         (coe du_0'60'half_146))
-- Once.Word.Width._.toℤ-negOne
d_toℤ'45'negOne_378 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_378 = erased
-- Once.Word.Width._.fromℤ-neg1
d_fromℤ'45'neg1_386 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_386 = erased
-- Once.Word.Width._.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_392 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_392 = erased
-- Once.Word.Width._._.toℤ-x-hi
d_toℤ'45'x'45'hi_418 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'x'45'hi_418 = erased
-- Once.Word.Width._.%ˢ-negOne
d_'37''738''45'negOne_424 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_424 = erased
-- Once.Word.Width._._.tmod-toℤ-negOne
d_tmod'45'toℤ'45'negOne_448 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'toℤ'45'negOne_448 = erased
-- Once.Word.Width._./ˢ-negOne
d_'47''738''45'negOne_452 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_452 = erased
-- Once.Word.Width._._.x≡intMin
d_x'8801'intMin_480 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x'8801'intMin_480 = erased
-- Once.Word.Width._./ˢ-in-range
d_'47''738''45'in'45'range_492 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_492 v0 ~v1 ~v2 v3 v4
  = du_'47''738''45'in'45'range_492 v0 v3 v4
du_'47''738''45'in'45'range_492 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'47''738''45'in'45'range_492 v0 v1 v2
  = let v3 = eqInt (coe v2) (coe (0 :: Integer)) in
    coe
      (if coe v3
         then coe du_negOne'60'modulus_360 (coe v0)
         else (let v4
                     = MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                         (coe eqInt (coe v1) (coe d_intMin_54 (coe v0)))
                         (coe eqInt (coe v2) (coe d_negOne_56 (coe v0))) in
               coe
                 (if coe v4
                    then coe du_half'60'modulus_352 (coe v0)
                    else coe
                           d_fromℤ'45'in'45'range_152 (coe v0)
                           (coe
                              du_tdivℤ_86 (coe d_toℤ_50 (coe v0) (coe v1))
                              (coe d_toℤ_50 (coe v0) (coe v2))))))
-- Once.Word.Width._.%ˢ-in-range
d_'37''738''45'in'45'range_526 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_526 v0 ~v1 ~v2 v3 v4 v5
  = du_'37''738''45'in'45'range_526 v0 v3 v4 v5
du_'37''738''45'in'45'range_526 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'37''738''45'in'45'range_526 v0 v1 v2 v3
  = let v4 = eqInt (coe v2) (coe (0 :: Integer)) in
    coe
      (if coe v4
         then coe v3
         else (let v5
                     = MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                         (coe eqInt (coe v1) (coe d_intMin_54 (coe v0)))
                         (coe eqInt (coe v2) (coe d_negOne_56 (coe v0))) in
               coe
                 (if coe v5
                    then coe du_0'60'modulus_144
                    else coe
                           d_fromℤ'45'in'45'range_152 (coe v0)
                           (coe
                              du_tmodℤ_88 (coe d_toℤ_50 (coe v0) (coe v1))
                              (coe d_toℤ_50 (coe v0) (coe v2))))))
-- Once.Word.Width.⊕≡+
d_'8853''8801''43'_570 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_570 = erased
-- Once.Word.Width.⊖≡∸
d_'8854''8801''8760'_582 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_582 = erased
-- Once.Word.Width._.y≤mod
d_y'8804'mod_596 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_y'8804'mod_596 ~v0 ~v1 ~v2 v3 v4 = du_y'8804'mod_596 v3 v4
du_y'8804'mod_596 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_y'8804'mod_596 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998 (coe v1))
-- Once.Word.Width.⊕-normʳ
d_'8853''45'norm'691'_602 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_602 = erased
-- Once.Word.Width.⊖-normʳ
d_'8854''45'norm'691'_614 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_614 = erased
-- Once.Word.Width.norm-id
d_norm'45'id_626 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_626 = erased
-- Once.Word.Width.1<modulus
d_1'60'modulus_628 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_628 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'94''45'mono'691''45''8804'_4502
      (coe (2 :: Integer)) (coe (1 :: Integer)) (coe v0) (coe v1)
-- Once.Word.Width.norm-0
d_norm'45'0_632 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_632 = erased
-- Once.Word.Width.⊕-neg-suc
d_'8853''45'neg'45'suc_638 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_638 = erased
-- Once.Word.Width.⊕-neg
d_'8853''45'neg_652 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_652 = erased
-- Once.Word.Word64._%ˢ_
d__'37''738'__668 :: Integer -> Integer -> Integer
d__'37''738'__668 = coe d__'37''738'__104 (coe (64 :: Integer))
-- Once.Word.Word64._/ˢ_
d__'47''738'__670 :: Integer -> Integer -> Integer
d__'47''738'__670 = coe d__'47''738'__98 (coe (64 :: Integer))
-- Once.Word.Word64._<ˢ_
d__'60''738'__672 :: Integer -> Integer -> Bool
d__'60''738'__672 = coe d__'60''738'__58 (coe (64 :: Integer))
-- Once.Word.Word64._≡ʷ_
d__'8801''695'__674 :: Integer -> Integer -> Bool
d__'8801''695'__674 = coe du__'8801''695'__64
-- Once.Word.Word64._⊕_
d__'8853'__676 :: Integer -> Integer -> Integer
d__'8853'__676 = coe d__'8853'__26 (coe (64 :: Integer))
-- Once.Word.Word64._⊖_
d__'8854'__678 :: Integer -> Integer -> Integer
d__'8854'__678 = coe d__'8854'__32 (coe (64 :: Integer))
-- Once.Word.Word64._⊗_
d__'8855'__680 :: Integer -> Integer -> Integer
d__'8855'__680 = coe d__'8855'__38 (coe (64 :: Integer))
-- Once.Word.Word64.%ˢ-else
d_'37''738''45'else_682 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_682 = erased
-- Once.Word.Word64.%ˢ-in-range
d_'37''738''45'in'45'range_684 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_684 v0 v1 v2 v3 v4
  = coe
      du_'37''738''45'in'45'range_526 (coe (64 :: Integer)) v2 v3 v4
-- Once.Word.Word64.%ˢ-mid
d_'37''738''45'mid_686 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_686 = erased
-- Once.Word.Word64.%ˢ-negOne
d_'37''738''45'negOne_688 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_688 = erased
-- Once.Word.Word64.%ˢ-zero
d_'37''738''45'zero_690 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_690 = erased
-- Once.Word.Word64./ˢ-else
d_'47''738''45'else_692 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_692 = erased
-- Once.Word.Word64./ˢ-in-range
d_'47''738''45'in'45'range_694 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_694 v0 v1 v2 v3
  = coe du_'47''738''45'in'45'range_492 (coe (64 :: Integer)) v2 v3
-- Once.Word.Word64./ˢ-mid
d_'47''738''45'mid_696 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_696 = erased
-- Once.Word.Word64./ˢ-negOne
d_'47''738''45'negOne_698 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_698 = erased
-- Once.Word.Word64./ˢ-pow2
d_'47''738''45'pow2_700 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_700 = erased
-- Once.Word.Word64./ˢ-zero
d_'47''738''45'zero_702 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_702 = erased
-- Once.Word.Word64.0<half
d_0'60'half_704 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_704 = coe du_0'60'half_146
-- Once.Word.Word64.0<modulus
d_0'60'modulus_706 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_706 = coe du_0'60'modulus_144
-- Once.Word.Word64.0<negOne
d_0'60'negOne_708 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_708 v0 v1
  = coe du_0'60'negOne_348 (coe (64 :: Integer))
-- Once.Word.Word64.1<modulus
d_1'60'modulus_710 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_710 = coe d_1'60'modulus_628 (coe (64 :: Integer))
-- Once.Word.Word64.2*n≡n+n
d_2'42'n'8801'n'43'n_712 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_712 = erased
-- Once.Word.Word64.2≤modulus
d_2'8804'modulus_714 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_714 v0 v1
  = coe du_2'8804'modulus_344 (coe (64 :: Integer))
-- Once.Word.Word64.Word
d_Word_716 :: ()
d_Word_716 = erased
-- Once.Word.Word64.fromℤ
d_fromℤ_718 :: Integer -> Integer
d_fromℤ_718 = coe d_fromℤ_20 (coe (64 :: Integer))
-- Once.Word.Word64.fromℤ-0
d_fromℤ'45'0_720 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_720 = erased
-- Once.Word.Word64.fromℤ-in-range
d_fromℤ'45'in'45'range_722 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_722
  = coe d_fromℤ'45'in'45'range_152 (coe (64 :: Integer))
-- Once.Word.Word64.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_724 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_724 = erased
-- Once.Word.Word64.fromℤ-neg1
d_fromℤ'45'neg1_726 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_726 = erased
-- Once.Word.Word64.half
d_half_728 :: Integer
d_half_728 = coe d_half_48 (coe (64 :: Integer))
-- Once.Word.Word64.half<modulus
d_half'60'modulus_730 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_730 v0 v1
  = coe du_half'60'modulus_352 (coe (64 :: Integer))
-- Once.Word.Word64.half≡2^b
d_half'8801'2'94'b_732 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_732 = erased
-- Once.Word.Word64.half≤negOne
d_half'8804'negOne_734 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_734 v0 v1
  = coe du_half'8804'negOne_372 (coe (64 :: Integer))
-- Once.Word.Word64.intMin
d_intMin_736 :: Integer
d_intMin_736 = coe d_intMin_54 (coe (64 :: Integer))
-- Once.Word.Word64.modulus
d_modulus_738 :: Integer
d_modulus_738 = coe d_modulus_10 (coe (64 :: Integer))
-- Once.Word.Word64.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_740 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_740 = erased
-- Once.Word.Word64.modulus≢0
d_modulus'8802'0_742 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_742
  = coe d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.Word.Word64.mod∸half≡half
d_mod'8760'half'8801'half_744 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_744 = erased
-- Once.Word.Word64.mod≡half+half
d_mod'8801'half'43'half_746 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_746 = erased
-- Once.Word.Word64.negOne
d_negOne_748 :: Integer
d_negOne_748 = coe d_negOne_56 (coe (64 :: Integer))
-- Once.Word.Word64.negOne<modulus
d_negOne'60'modulus_750 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_750 v0 v1
  = coe du_negOne'60'modulus_360 (coe (64 :: Integer))
-- Once.Word.Word64.negOne≢0
d_negOne'8802'0_752 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_752 = erased
-- Once.Word.Word64.norm
d_norm_754 :: Integer -> Integer
d_norm_754 = coe d_norm_16 (coe (64 :: Integer))
-- Once.Word.Word64.norm-0
d_norm'45'0_756 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_756 = erased
-- Once.Word.Word64.norm-id
d_norm'45'id_758 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_758 = erased
-- Once.Word.Word64.sdiv2ᵏ
d_sdiv2'7503'_760 :: Integer -> Integer -> Integer
d_sdiv2'7503'_760 = coe d_sdiv2'7503'_116 (coe (64 :: Integer))
-- Once.Word.Word64.shlᵂ
d_shl'7490'_762 :: Integer -> Integer -> Integer
d_shl'7490'_762 = coe d_shl'7490'_110 (coe (64 :: Integer))
-- Once.Word.Word64.sucNegOne≡mod
d_sucNegOne'8801'mod_764 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_764 = erased
-- Once.Word.Word64.tdiv-neg1
d_tdiv'45'neg1_766 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_766 = erased
-- Once.Word.Word64.tmod-neg1
d_tmod'45'neg1_768 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_768 = erased
-- Once.Word.Word64.toℤ
d_toℤ_770 :: Integer -> Integer
d_toℤ_770 = coe d_toℤ_50 (coe (64 :: Integer))
-- Once.Word.Word64.toℤ-negOne
d_toℤ'45'negOne_772 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_772 = erased
-- Once.Word.Word64.≡ᵇ-refl
d_'8801''7495''45'refl_774 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_774 = erased
-- Once.Word.Word64.≡ᵇ0-false
d_'8801''7495'0'45'false_776 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_776 = erased
-- Once.Word.Word64.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_778 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_778 = erased
-- Once.Word.Word64.⊕-neg
d_'8853''45'neg_780 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_780 = erased
-- Once.Word.Word64.⊕-neg-suc
d_'8853''45'neg'45'suc_782 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_782 = erased
-- Once.Word.Word64.⊕-normʳ
d_'8853''45'norm'691'_784 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_784 = erased
-- Once.Word.Word64.⊕≡+
d_'8853''8801''43'_786 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_786 = erased
-- Once.Word.Word64.⊖-normʳ
d_'8854''45'norm'691'_788 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_788 = erased
-- Once.Word.Word64.⊖≡∸
d_'8854''8801''8760'_790 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_790 = erased
-- Once.Word.Word64.⊗-pow2
d_'8855''45'pow2_792 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_792 = erased
-- Once.Word.Word64.⊝_
d_'8861'__794 :: Integer -> Integer
d_'8861'__794 = coe d_'8861'__44 (coe (64 :: Integer))
-- Once.Word.Word64.⊝-intMin
d_'8861''45'intMin_796 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_796 = erased
