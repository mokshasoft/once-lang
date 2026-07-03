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
-- Once.Word.Width.0<modulus
d_0'60'modulus_110 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_110 ~v0 = du_0'60'modulus_110
du_0'60'modulus_110 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'modulus_110
  = coe MAlonzo.Code.Data.Nat.Properties.du_m'94'n'62'0_4482
-- Once.Word.Width.0<half
d_0'60'half_112 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_112 ~v0 = du_0'60'half_112
du_0'60'half_112 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'half_112
  = coe MAlonzo.Code.Data.Nat.Properties.du_m'94'n'62'0_4482
-- Once.Word.Width.fromℤ-0
d_fromℤ'45'0_114 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_114 = erased
-- Once.Word.Width.fromℤ-in-range
d_fromℤ'45'in'45'range_118 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_118 v0 v1
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
d_'47''738''45'zero_126 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_126 = erased
-- Once.Word.Width.%ˢ-zero
d_'37''738''45'zero_132 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_132 = erased
-- Once.Word.Width.≡ᵇ-refl
d_'8801''7495''45'refl_138 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_138 = erased
-- Once.Word.Width.≡ᵇ0-false
d_'8801''7495'0'45'false_144 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_144 = erased
-- Once.Word.Width.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_150 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_150 = erased
-- Once.Word.Width./ˢ-else
d_'47''738''45'else_180 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_180 = erased
-- Once.Word.Width./ˢ-mid
d_'47''738''45'mid_202 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_202 = erased
-- Once.Word.Width.%ˢ-else
d_'37''738''45'else_224 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_224 = erased
-- Once.Word.Width.%ˢ-mid
d_'37''738''45'mid_246 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_246 = erased
-- Once.Word.Width.tdiv-neg1
d_tdiv'45'neg1_266 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_266 = erased
-- Once.Word.Width.tmod-neg1
d_tmod'45'neg1_278 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_278 = erased
-- Once.Word.Width._.half≡2^b
d_half'8801'2'94'b_292 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_292 = erased
-- Once.Word.Width._.2*n≡n+n
d_2'42'n'8801'n'43'n_298 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_298 = erased
-- Once.Word.Width._.mod≡half+half
d_mod'8801'half'43'half_304 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_304 = erased
-- Once.Word.Width._.2≤modulus
d_2'8804'modulus_310 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_310 v0 ~v1 ~v2 = du_2'8804'modulus_310 v0
du_2'8804'modulus_310 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_2'8804'modulus_310 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'45''8804'_3672
      (coe d_half_48 (coe v0)) (coe du_0'60'half_112)
      (coe du_0'60'half_112)
-- Once.Word.Width._.0<negOne
d_0'60'negOne_314 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_314 v0 ~v1 ~v2 = du_0'60'negOne_314 v0
du_0'60'negOne_314 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'negOne_314 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'737''45''8804'_5232
      (coe (2 :: Integer)) (coe d_modulus_10 (coe v0))
      (coe (1 :: Integer)) (coe du_2'8804'modulus_310 (coe v0))
-- Once.Word.Width._.negOne≢0
d_negOne'8802'0_316 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_316 = erased
-- Once.Word.Width._.half<modulus
d_half'60'modulus_318 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_318 v0 ~v1 ~v2 = du_half'60'modulus_318 v0
du_half'60'modulus_318 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_half'60'modulus_318 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3714
      (coe d_half_48 (coe v0)) (coe du_0'60'half_112)
-- Once.Word.Width._.sucNegOne≡mod
d_sucNegOne'8801'mod_324 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_324 = erased
-- Once.Word.Width._.negOne<modulus
d_negOne'60'modulus_326 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_326 v0 ~v1 ~v2 = du_negOne'60'modulus_326 v0
du_negOne'60'modulus_326 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_negOne'60'modulus_326 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (1 :: Integer)) (coe d_negOne_56 (coe v0)))
-- Once.Word.Width._.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_330 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_330 = erased
-- Once.Word.Width._.mod∸half≡half
d_mod'8760'half'8801'half_332 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_332 = erased
-- Once.Word.Width._.⊝-intMin
d_'8861''45'intMin_336 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_336 = erased
-- Once.Word.Width._.half≤negOne
d_half'8804'negOne_338 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_338 v0 ~v1 ~v2 = du_half'8804'negOne_338 v0
du_half'8804'negOne_338 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_half'8804'negOne_338 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'737''45''8804'_5232
      (coe addInt (coe (1 :: Integer)) (coe d_half_48 (coe v0)))
      (coe addInt (coe d_half_48 (coe v0)) (coe d_half_48 (coe v0)))
      (coe (1 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         (d_half_48 (coe v0)) (1 :: Integer) (d_half_48 (coe v0))
         (coe du_0'60'half_112))
-- Once.Word.Width._.toℤ-negOne
d_toℤ'45'negOne_344 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_344 = erased
-- Once.Word.Width._.fromℤ-neg1
d_fromℤ'45'neg1_352 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_352 = erased
-- Once.Word.Width._.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_358 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_358 = erased
-- Once.Word.Width._._.toℤ-x-hi
d_toℤ'45'x'45'hi_384 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'x'45'hi_384 = erased
-- Once.Word.Width._.%ˢ-negOne
d_'37''738''45'negOne_390 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_390 = erased
-- Once.Word.Width._._.tmod-toℤ-negOne
d_tmod'45'toℤ'45'negOne_414 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'toℤ'45'negOne_414 = erased
-- Once.Word.Width._./ˢ-negOne
d_'47''738''45'negOne_418 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_418 = erased
-- Once.Word.Width._._.x≡intMin
d_x'8801'intMin_446 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x'8801'intMin_446 = erased
-- Once.Word.Width._./ˢ-in-range
d_'47''738''45'in'45'range_458 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_458 v0 ~v1 ~v2 v3 v4
  = du_'47''738''45'in'45'range_458 v0 v3 v4
du_'47''738''45'in'45'range_458 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'47''738''45'in'45'range_458 v0 v1 v2
  = let v3 = eqInt (coe v2) (coe (0 :: Integer)) in
    coe
      (if coe v3
         then coe du_negOne'60'modulus_326 (coe v0)
         else (let v4
                     = MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                         (coe eqInt (coe v1) (coe d_intMin_54 (coe v0)))
                         (coe eqInt (coe v2) (coe d_negOne_56 (coe v0))) in
               coe
                 (if coe v4
                    then coe du_half'60'modulus_318 (coe v0)
                    else coe
                           d_fromℤ'45'in'45'range_118 (coe v0)
                           (coe
                              du_tdivℤ_86 (coe d_toℤ_50 (coe v0) (coe v1))
                              (coe d_toℤ_50 (coe v0) (coe v2))))))
-- Once.Word.Width._.%ˢ-in-range
d_'37''738''45'in'45'range_492 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_492 v0 ~v1 ~v2 v3 v4 v5
  = du_'37''738''45'in'45'range_492 v0 v3 v4 v5
du_'37''738''45'in'45'range_492 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'37''738''45'in'45'range_492 v0 v1 v2 v3
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
                    then coe du_0'60'modulus_110
                    else coe
                           d_fromℤ'45'in'45'range_118 (coe v0)
                           (coe
                              du_tmodℤ_88 (coe d_toℤ_50 (coe v0) (coe v1))
                              (coe d_toℤ_50 (coe v0) (coe v2))))))
-- Once.Word.Word64._%ˢ_
d__'37''738'__534 :: Integer -> Integer -> Integer
d__'37''738'__534 = coe d__'37''738'__104 (coe (64 :: Integer))
-- Once.Word.Word64._/ˢ_
d__'47''738'__536 :: Integer -> Integer -> Integer
d__'47''738'__536 = coe d__'47''738'__98 (coe (64 :: Integer))
-- Once.Word.Word64._<ˢ_
d__'60''738'__538 :: Integer -> Integer -> Bool
d__'60''738'__538 = coe d__'60''738'__58 (coe (64 :: Integer))
-- Once.Word.Word64._≡ʷ_
d__'8801''695'__540 :: Integer -> Integer -> Bool
d__'8801''695'__540 = coe du__'8801''695'__64
-- Once.Word.Word64._⊕_
d__'8853'__542 :: Integer -> Integer -> Integer
d__'8853'__542 = coe d__'8853'__26 (coe (64 :: Integer))
-- Once.Word.Word64._⊖_
d__'8854'__544 :: Integer -> Integer -> Integer
d__'8854'__544 = coe d__'8854'__32 (coe (64 :: Integer))
-- Once.Word.Word64._⊗_
d__'8855'__546 :: Integer -> Integer -> Integer
d__'8855'__546 = coe d__'8855'__38 (coe (64 :: Integer))
-- Once.Word.Word64.%ˢ-else
d_'37''738''45'else_548 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_548 = erased
-- Once.Word.Word64.%ˢ-in-range
d_'37''738''45'in'45'range_550 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_550 v0 v1 v2 v3 v4
  = coe
      du_'37''738''45'in'45'range_492 (coe (64 :: Integer)) v2 v3 v4
-- Once.Word.Word64.%ˢ-mid
d_'37''738''45'mid_552 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_552 = erased
-- Once.Word.Word64.%ˢ-negOne
d_'37''738''45'negOne_554 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_554 = erased
-- Once.Word.Word64.%ˢ-zero
d_'37''738''45'zero_556 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_556 = erased
-- Once.Word.Word64./ˢ-else
d_'47''738''45'else_558 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_558 = erased
-- Once.Word.Word64./ˢ-in-range
d_'47''738''45'in'45'range_560 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_560 v0 v1 v2 v3
  = coe du_'47''738''45'in'45'range_458 (coe (64 :: Integer)) v2 v3
-- Once.Word.Word64./ˢ-mid
d_'47''738''45'mid_562 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_562 = erased
-- Once.Word.Word64./ˢ-negOne
d_'47''738''45'negOne_564 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_564 = erased
-- Once.Word.Word64./ˢ-zero
d_'47''738''45'zero_566 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_566 = erased
-- Once.Word.Word64.0<half
d_0'60'half_568 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_568 = coe du_0'60'half_112
-- Once.Word.Word64.0<modulus
d_0'60'modulus_570 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_570 = coe du_0'60'modulus_110
-- Once.Word.Word64.0<negOne
d_0'60'negOne_572 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_572 v0 v1
  = coe du_0'60'negOne_314 (coe (64 :: Integer))
-- Once.Word.Word64.2*n≡n+n
d_2'42'n'8801'n'43'n_574 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_574 = erased
-- Once.Word.Word64.2≤modulus
d_2'8804'modulus_576 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_576 v0 v1
  = coe du_2'8804'modulus_310 (coe (64 :: Integer))
-- Once.Word.Word64.Word
d_Word_578 :: ()
d_Word_578 = erased
-- Once.Word.Word64.fromℤ
d_fromℤ_580 :: Integer -> Integer
d_fromℤ_580 = coe d_fromℤ_20 (coe (64 :: Integer))
-- Once.Word.Word64.fromℤ-0
d_fromℤ'45'0_582 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_582 = erased
-- Once.Word.Word64.fromℤ-in-range
d_fromℤ'45'in'45'range_584 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_584
  = coe d_fromℤ'45'in'45'range_118 (coe (64 :: Integer))
-- Once.Word.Word64.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_586 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_586 = erased
-- Once.Word.Word64.fromℤ-neg1
d_fromℤ'45'neg1_588 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_588 = erased
-- Once.Word.Word64.half
d_half_590 :: Integer
d_half_590 = coe d_half_48 (coe (64 :: Integer))
-- Once.Word.Word64.half<modulus
d_half'60'modulus_592 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_592 v0 v1
  = coe du_half'60'modulus_318 (coe (64 :: Integer))
-- Once.Word.Word64.half≡2^b
d_half'8801'2'94'b_594 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_594 = erased
-- Once.Word.Word64.half≤negOne
d_half'8804'negOne_596 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_596 v0 v1
  = coe du_half'8804'negOne_338 (coe (64 :: Integer))
-- Once.Word.Word64.intMin
d_intMin_598 :: Integer
d_intMin_598 = coe d_intMin_54 (coe (64 :: Integer))
-- Once.Word.Word64.modulus
d_modulus_600 :: Integer
d_modulus_600 = coe d_modulus_10 (coe (64 :: Integer))
-- Once.Word.Word64.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_602 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_602 = erased
-- Once.Word.Word64.modulus≢0
d_modulus'8802'0_604 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_604
  = coe d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.Word.Word64.mod∸half≡half
d_mod'8760'half'8801'half_606 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_606 = erased
-- Once.Word.Word64.mod≡half+half
d_mod'8801'half'43'half_608 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_608 = erased
-- Once.Word.Word64.negOne
d_negOne_610 :: Integer
d_negOne_610 = coe d_negOne_56 (coe (64 :: Integer))
-- Once.Word.Word64.negOne<modulus
d_negOne'60'modulus_612 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_612 v0 v1
  = coe du_negOne'60'modulus_326 (coe (64 :: Integer))
-- Once.Word.Word64.negOne≢0
d_negOne'8802'0_614 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_614 = erased
-- Once.Word.Word64.norm
d_norm_616 :: Integer -> Integer
d_norm_616 = coe d_norm_16 (coe (64 :: Integer))
-- Once.Word.Word64.sucNegOne≡mod
d_sucNegOne'8801'mod_618 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_618 = erased
-- Once.Word.Word64.tdiv-neg1
d_tdiv'45'neg1_620 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_620 = erased
-- Once.Word.Word64.tmod-neg1
d_tmod'45'neg1_622 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_622 = erased
-- Once.Word.Word64.toℤ
d_toℤ_624 :: Integer -> Integer
d_toℤ_624 = coe d_toℤ_50 (coe (64 :: Integer))
-- Once.Word.Word64.toℤ-negOne
d_toℤ'45'negOne_626 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_626 = erased
-- Once.Word.Word64.≡ᵇ-refl
d_'8801''7495''45'refl_628 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_628 = erased
-- Once.Word.Word64.≡ᵇ0-false
d_'8801''7495'0'45'false_630 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_630 = erased
-- Once.Word.Word64.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_632 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_632 = erased
-- Once.Word.Word64.⊝_
d_'8861'__634 :: Integer -> Integer
d_'8861'__634 = coe d_'8861'__44 (coe (64 :: Integer))
-- Once.Word.Word64.⊝-intMin
d_'8861''45'intMin_636 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_636 = erased
