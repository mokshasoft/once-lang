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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
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
-- Once.Word.Width.InRange
d_InRange_56 :: Integer -> Integer -> ()
d_InRange_56 = erased
-- Once.Word.Width.inRange?
d_inRange'63'_62 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_62 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
      (coe
         MAlonzo.Code.Data.Integer.Properties.d__'8804''63'__2880
         (coe
            MAlonzo.Code.Data.Integer.Base.d_'45'__260
            (coe d_half_48 (coe v0)))
         (coe v1))
      (coe
         MAlonzo.Code.Data.Integer.Properties.d__'8804''63'__2880 (coe v1)
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_half_48 (coe v0))
            (1 :: Integer)))
-- Once.Word.Width.toWord
d_toWord_68 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_68 v0 v1 ~v2 = du_toWord_68 v0 v1
du_toWord_68 :: Integer -> Integer -> Integer
du_toWord_68 v0 v1 = coe d_fromℤ_20 (coe v0) (coe v1)
-- Once.Word.Width.toWord≡fromℤ
d_toWord'8801'fromℤ_76 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'8801'fromℤ_76 = erased
-- Once.Word.Width.negOne
d_negOne_78 :: Integer -> Integer
d_negOne_78 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_modulus_10 (coe v0))
      (1 :: Integer)
-- Once.Word.Width._<ˢ_
d__'60''738'__80 :: Integer -> Integer -> Integer -> Bool
d__'60''738'__80 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
      (coe
         MAlonzo.Code.Data.Integer.Properties.d__'60''63'__3190
         (coe d_toℤ_50 (coe v0) (coe v1)) (coe d_toℤ_50 (coe v0) (coe v2)))
-- Once.Word.Width._≡ʷ_
d__'8801''695'__86 :: Integer -> Integer -> Integer -> Bool
d__'8801''695'__86 ~v0 v1 v2 = du__'8801''695'__86 v1 v2
du__'8801''695'__86 :: Integer -> Integer -> Bool
du__'8801''695'__86 v0 v1 = coe eqInt (coe v0) (coe v1)
-- Once.Word.Width._divℕ_
d__divℕ__92 :: Integer -> Integer -> Integer -> Integer
d__divℕ__92 ~v0 v1 v2 = du__divℕ__92 v1 v2
du__divℕ__92 :: Integer -> Integer -> Integer
du__divℕ__92 v0 v1
  = case coe v1 of
      0 -> coe (0 :: Integer)
      _ -> coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1)
-- Once.Word.Width._modℕ_
d__modℕ__94 :: Integer -> Integer -> Integer -> Integer
d__modℕ__94 ~v0 v1 v2 = du__modℕ__94 v1 v2
du__modℕ__94 :: Integer -> Integer -> Integer
du__modℕ__94 v0 v1
  = case coe v1 of
      0 -> coe v0
      _ -> coe MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v0) (coe v1)
-- Once.Word.Width.tdivℤ
d_tdivℤ_108 :: Integer -> Integer -> Integer -> Integer
d_tdivℤ_108 ~v0 v1 v2 = du_tdivℤ_108 v1 v2
du_tdivℤ_108 :: Integer -> Integer -> Integer
du_tdivℤ_108 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'9667'__238
      (coe
         MAlonzo.Code.Data.Sign.Base.d__'42'__14
         (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v0))
         (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v1)))
      (coe
         du__divℕ__92
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
-- Once.Word.Width.tmodℤ
d_tmodℤ_110 :: Integer -> Integer -> Integer -> Integer
d_tmodℤ_110 ~v0 v1 v2 = du_tmodℤ_110 v1 v2
du_tmodℤ_110 :: Integer -> Integer -> Integer
du_tmodℤ_110 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'9667'__238
      (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v0))
      (coe
         du__modℕ__94
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
-- Once.Word.Width._/ˢ_
d__'47''738'__120 :: Integer -> Integer -> Integer -> Integer
d__'47''738'__120 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v2) (coe (0 :: Integer)))
      (coe d_negOne_78 (coe v0))
      (coe
         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8743'__24
            (coe eqInt (coe v1) (coe d_intMin_54 (coe v0)))
            (coe eqInt (coe v2) (coe d_negOne_78 (coe v0))))
         (coe d_intMin_54 (coe v0))
         (coe
            d_fromℤ_20 (coe v0)
            (coe
               du_tdivℤ_108 (coe d_toℤ_50 (coe v0) (coe v1))
               (coe d_toℤ_50 (coe v0) (coe v2)))))
-- Once.Word.Width._%ˢ_
d__'37''738'__126 :: Integer -> Integer -> Integer -> Integer
d__'37''738'__126 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v2) (coe (0 :: Integer))) (coe v1)
      (coe
         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8743'__24
            (coe eqInt (coe v1) (coe d_intMin_54 (coe v0)))
            (coe eqInt (coe v2) (coe d_negOne_78 (coe v0))))
         (coe (0 :: Integer))
         (coe
            d_fromℤ_20 (coe v0)
            (coe
               du_tmodℤ_110 (coe d_toℤ_50 (coe v0) (coe v1))
               (coe d_toℤ_50 (coe v0) (coe v2)))))
-- Once.Word.Width.shlᵂ
d_shl'7490'_132 :: Integer -> Integer -> Integer -> Integer
d_shl'7490'_132 v0 v1 v2
  = coe
      d_norm_16 (coe v0)
      (coe
         mulInt (coe v1)
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe v2)))
-- Once.Word.Width.sdiv2ᵏ
d_sdiv2'7503'_138 :: Integer -> Integer -> Integer -> Integer
d_sdiv2'7503'_138 v0 v1 v2
  = coe
      d__'47''738'__120 (coe v0) (coe v1)
      (coe
         d_fromℤ_20 (coe v0)
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe v2)))
-- Once.Word.Width.⊗-pow2
d_'8855''45'pow2_148 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_148 = erased
-- Once.Word.Width./ˢ-pow2
d_'47''738''45'pow2_160 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_160 = erased
-- Once.Word.Width.0<modulus
d_0'60'modulus_166 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_166 ~v0 = du_0'60'modulus_166
du_0'60'modulus_166 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'modulus_166
  = coe MAlonzo.Code.Data.Nat.Properties.du_m'94'n'62'0_4482
-- Once.Word.Width.0<half
d_0'60'half_168 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_168 ~v0 = du_0'60'half_168
du_0'60'half_168 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'half_168
  = coe MAlonzo.Code.Data.Nat.Properties.du_m'94'n'62'0_4482
-- Once.Word.Width.fromℤ-0
d_fromℤ'45'0_170 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_170 = erased
-- Once.Word.Width.fromℤ-in-range
d_fromℤ'45'in'45'range_174 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_174 v0 v1
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
d_'47''738''45'zero_182 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_182 = erased
-- Once.Word.Width.%ˢ-zero
d_'37''738''45'zero_188 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_188 = erased
-- Once.Word.Width.≡ᵇ-refl
d_'8801''7495''45'refl_194 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_194 = erased
-- Once.Word.Width.≡ᵇ0-false
d_'8801''7495'0'45'false_200 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_200 = erased
-- Once.Word.Width.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_206 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_206 = erased
-- Once.Word.Width./ˢ-else
d_'47''738''45'else_236 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_236 = erased
-- Once.Word.Width./ˢ-mid
d_'47''738''45'mid_258 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_258 = erased
-- Once.Word.Width.%ˢ-else
d_'37''738''45'else_280 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_280 = erased
-- Once.Word.Width.%ˢ-mid
d_'37''738''45'mid_302 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_302 = erased
-- Once.Word.Width.tdiv-neg1
d_tdiv'45'neg1_322 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_322 = erased
-- Once.Word.Width.tmod-neg1
d_tmod'45'neg1_334 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_334 = erased
-- Once.Word.Width._.half≡2^b
d_half'8801'2'94'b_348 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_348 = erased
-- Once.Word.Width._.2*n≡n+n
d_2'42'n'8801'n'43'n_354 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_354 = erased
-- Once.Word.Width._.mod≡half+half
d_mod'8801'half'43'half_360 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_360 = erased
-- Once.Word.Width._.2≤modulus
d_2'8804'modulus_366 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_366 v0 ~v1 ~v2 = du_2'8804'modulus_366 v0
du_2'8804'modulus_366 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_2'8804'modulus_366 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'45''8804'_3672
      (coe d_half_48 (coe v0)) (coe du_0'60'half_168)
      (coe du_0'60'half_168)
-- Once.Word.Width._.0<negOne
d_0'60'negOne_370 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_370 v0 ~v1 ~v2 = du_0'60'negOne_370 v0
du_0'60'negOne_370 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'negOne_370 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'737''45''8804'_5232
      (coe (2 :: Integer)) (coe d_modulus_10 (coe v0))
      (coe (1 :: Integer)) (coe du_2'8804'modulus_366 (coe v0))
-- Once.Word.Width._.negOne≢0
d_negOne'8802'0_372 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_372 = erased
-- Once.Word.Width._.half<modulus
d_half'60'modulus_374 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_374 v0 ~v1 ~v2 = du_half'60'modulus_374 v0
du_half'60'modulus_374 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_half'60'modulus_374 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3714
      (coe d_half_48 (coe v0)) (coe du_0'60'half_168)
-- Once.Word.Width._.sucNegOne≡mod
d_sucNegOne'8801'mod_380 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_380 = erased
-- Once.Word.Width._.negOne<modulus
d_negOne'60'modulus_382 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_382 v0 ~v1 ~v2 = du_negOne'60'modulus_382 v0
du_negOne'60'modulus_382 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_negOne'60'modulus_382 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (1 :: Integer)) (coe d_negOne_78 (coe v0)))
-- Once.Word.Width._.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_386 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_386 = erased
-- Once.Word.Width._.mod∸half≡half
d_mod'8760'half'8801'half_388 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_388 = erased
-- Once.Word.Width._.⊝-intMin
d_'8861''45'intMin_392 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_392 = erased
-- Once.Word.Width._.half≤negOne
d_half'8804'negOne_394 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_394 v0 ~v1 ~v2 = du_half'8804'negOne_394 v0
du_half'8804'negOne_394 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_half'8804'negOne_394 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'737''45''8804'_5232
      (coe addInt (coe (1 :: Integer)) (coe d_half_48 (coe v0)))
      (coe addInt (coe d_half_48 (coe v0)) (coe d_half_48 (coe v0)))
      (coe (1 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         (d_half_48 (coe v0)) (1 :: Integer) (d_half_48 (coe v0))
         (coe du_0'60'half_168))
-- Once.Word.Width._.toℤ-negOne
d_toℤ'45'negOne_400 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_400 = erased
-- Once.Word.Width._.fromℤ-neg1
d_fromℤ'45'neg1_408 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_408 = erased
-- Once.Word.Width._.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_414 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_414 = erased
-- Once.Word.Width._._.toℤ-x-hi
d_toℤ'45'x'45'hi_440 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'x'45'hi_440 = erased
-- Once.Word.Width._.%ˢ-negOne
d_'37''738''45'negOne_446 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_446 = erased
-- Once.Word.Width._._.tmod-toℤ-negOne
d_tmod'45'toℤ'45'negOne_470 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'toℤ'45'negOne_470 = erased
-- Once.Word.Width._./ˢ-negOne
d_'47''738''45'negOne_474 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_474 = erased
-- Once.Word.Width._._.x≡intMin
d_x'8801'intMin_502 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x'8801'intMin_502 = erased
-- Once.Word.Width._./ˢ-in-range
d_'47''738''45'in'45'range_514 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_514 v0 ~v1 ~v2 v3 v4
  = du_'47''738''45'in'45'range_514 v0 v3 v4
du_'47''738''45'in'45'range_514 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'47''738''45'in'45'range_514 v0 v1 v2
  = let v3 = eqInt (coe v2) (coe (0 :: Integer)) in
    coe
      (if coe v3
         then coe du_negOne'60'modulus_382 (coe v0)
         else (let v4
                     = MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                         (coe eqInt (coe v1) (coe d_intMin_54 (coe v0)))
                         (coe eqInt (coe v2) (coe d_negOne_78 (coe v0))) in
               coe
                 (if coe v4
                    then coe du_half'60'modulus_374 (coe v0)
                    else coe
                           d_fromℤ'45'in'45'range_174 (coe v0)
                           (coe
                              du_tdivℤ_108 (coe d_toℤ_50 (coe v0) (coe v1))
                              (coe d_toℤ_50 (coe v0) (coe v2))))))
-- Once.Word.Width._.%ˢ-in-range
d_'37''738''45'in'45'range_548 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_548 v0 ~v1 ~v2 v3 v4 v5
  = du_'37''738''45'in'45'range_548 v0 v3 v4 v5
du_'37''738''45'in'45'range_548 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'37''738''45'in'45'range_548 v0 v1 v2 v3
  = let v4 = eqInt (coe v2) (coe (0 :: Integer)) in
    coe
      (if coe v4
         then coe v3
         else (let v5
                     = MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                         (coe eqInt (coe v1) (coe d_intMin_54 (coe v0)))
                         (coe eqInt (coe v2) (coe d_negOne_78 (coe v0))) in
               coe
                 (if coe v5
                    then coe du_0'60'modulus_166
                    else coe
                           d_fromℤ'45'in'45'range_174 (coe v0)
                           (coe
                              du_tmodℤ_110 (coe d_toℤ_50 (coe v0) (coe v1))
                              (coe d_toℤ_50 (coe v0) (coe v2))))))
-- Once.Word.Width.⊕≡+
d_'8853''8801''43'_592 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_592 = erased
-- Once.Word.Width.⊖≡∸
d_'8854''8801''8760'_604 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_604 = erased
-- Once.Word.Width._.y≤mod
d_y'8804'mod_618 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_y'8804'mod_618 ~v0 ~v1 ~v2 v3 v4 = du_y'8804'mod_618 v3 v4
du_y'8804'mod_618 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_y'8804'mod_618 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998 (coe v1))
-- Once.Word.Width.⊕-normʳ
d_'8853''45'norm'691'_624 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_624 = erased
-- Once.Word.Width.⊖-normʳ
d_'8854''45'norm'691'_636 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_636 = erased
-- Once.Word.Width.norm-id
d_norm'45'id_648 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_648 = erased
-- Once.Word.Width.1<modulus
d_1'60'modulus_650 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_650 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'94''45'mono'691''45''8804'_4502
      (coe (2 :: Integer)) (coe (1 :: Integer)) (coe v0) (coe v1)
-- Once.Word.Width.norm-0
d_norm'45'0_654 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_654 = erased
-- Once.Word.Width.⊕-neg-suc
d_'8853''45'neg'45'suc_660 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_660 = erased
-- Once.Word.Width.⊕-neg
d_'8853''45'neg_674 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_674 = erased
-- Once.Word.Word64._%ˢ_
d__'37''738'__690 :: Integer -> Integer -> Integer
d__'37''738'__690 = coe d__'37''738'__126 (coe (64 :: Integer))
-- Once.Word.Word64._/ˢ_
d__'47''738'__692 :: Integer -> Integer -> Integer
d__'47''738'__692 = coe d__'47''738'__120 (coe (64 :: Integer))
-- Once.Word.Word64._<ˢ_
d__'60''738'__694 :: Integer -> Integer -> Bool
d__'60''738'__694 = coe d__'60''738'__80 (coe (64 :: Integer))
-- Once.Word.Word64._≡ʷ_
d__'8801''695'__696 :: Integer -> Integer -> Bool
d__'8801''695'__696 = coe du__'8801''695'__86
-- Once.Word.Word64._⊕_
d__'8853'__698 :: Integer -> Integer -> Integer
d__'8853'__698 = coe d__'8853'__26 (coe (64 :: Integer))
-- Once.Word.Word64._⊖_
d__'8854'__700 :: Integer -> Integer -> Integer
d__'8854'__700 = coe d__'8854'__32 (coe (64 :: Integer))
-- Once.Word.Word64._⊗_
d__'8855'__702 :: Integer -> Integer -> Integer
d__'8855'__702 = coe d__'8855'__38 (coe (64 :: Integer))
-- Once.Word.Word64.%ˢ-else
d_'37''738''45'else_704 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_704 = erased
-- Once.Word.Word64.%ˢ-in-range
d_'37''738''45'in'45'range_706 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_706 v0 v1 v2 v3 v4
  = coe
      du_'37''738''45'in'45'range_548 (coe (64 :: Integer)) v2 v3 v4
-- Once.Word.Word64.%ˢ-mid
d_'37''738''45'mid_708 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_708 = erased
-- Once.Word.Word64.%ˢ-negOne
d_'37''738''45'negOne_710 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_710 = erased
-- Once.Word.Word64.%ˢ-zero
d_'37''738''45'zero_712 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_712 = erased
-- Once.Word.Word64./ˢ-else
d_'47''738''45'else_714 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_714 = erased
-- Once.Word.Word64./ˢ-in-range
d_'47''738''45'in'45'range_716 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_716 v0 v1 v2 v3
  = coe du_'47''738''45'in'45'range_514 (coe (64 :: Integer)) v2 v3
-- Once.Word.Word64./ˢ-mid
d_'47''738''45'mid_718 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_718 = erased
-- Once.Word.Word64./ˢ-negOne
d_'47''738''45'negOne_720 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_720 = erased
-- Once.Word.Word64./ˢ-pow2
d_'47''738''45'pow2_722 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_722 = erased
-- Once.Word.Word64./ˢ-zero
d_'47''738''45'zero_724 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_724 = erased
-- Once.Word.Word64.0<half
d_0'60'half_726 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_726 = coe du_0'60'half_168
-- Once.Word.Word64.0<modulus
d_0'60'modulus_728 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_728 = coe du_0'60'modulus_166
-- Once.Word.Word64.0<negOne
d_0'60'negOne_730 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_730 v0 v1
  = coe du_0'60'negOne_370 (coe (64 :: Integer))
-- Once.Word.Word64.1<modulus
d_1'60'modulus_732 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_732 = coe d_1'60'modulus_650 (coe (64 :: Integer))
-- Once.Word.Word64.2*n≡n+n
d_2'42'n'8801'n'43'n_734 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_734 = erased
-- Once.Word.Word64.2≤modulus
d_2'8804'modulus_736 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_736 v0 v1
  = coe du_2'8804'modulus_366 (coe (64 :: Integer))
-- Once.Word.Word64.InRange
d_InRange_738 :: Integer -> ()
d_InRange_738 = erased
-- Once.Word.Word64.Word
d_Word_740 :: ()
d_Word_740 = erased
-- Once.Word.Word64.fromℤ
d_fromℤ_742 :: Integer -> Integer
d_fromℤ_742 = coe d_fromℤ_20 (coe (64 :: Integer))
-- Once.Word.Word64.fromℤ-0
d_fromℤ'45'0_744 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_744 = erased
-- Once.Word.Word64.fromℤ-in-range
d_fromℤ'45'in'45'range_746 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_746
  = coe d_fromℤ'45'in'45'range_174 (coe (64 :: Integer))
-- Once.Word.Word64.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_748 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_748 = erased
-- Once.Word.Word64.fromℤ-neg1
d_fromℤ'45'neg1_750 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_750 = erased
-- Once.Word.Word64.half
d_half_752 :: Integer
d_half_752 = coe d_half_48 (coe (64 :: Integer))
-- Once.Word.Word64.half<modulus
d_half'60'modulus_754 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_754 v0 v1
  = coe du_half'60'modulus_374 (coe (64 :: Integer))
-- Once.Word.Word64.half≡2^b
d_half'8801'2'94'b_756 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_756 = erased
-- Once.Word.Word64.half≤negOne
d_half'8804'negOne_758 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_758 v0 v1
  = coe du_half'8804'negOne_394 (coe (64 :: Integer))
-- Once.Word.Word64.inRange?
d_inRange'63'_760 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_760 = coe d_inRange'63'_62 (coe (64 :: Integer))
-- Once.Word.Word64.intMin
d_intMin_762 :: Integer
d_intMin_762 = coe d_intMin_54 (coe (64 :: Integer))
-- Once.Word.Word64.modulus
d_modulus_764 :: Integer
d_modulus_764 = coe d_modulus_10 (coe (64 :: Integer))
-- Once.Word.Word64.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_766 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_766 = erased
-- Once.Word.Word64.modulus≢0
d_modulus'8802'0_768 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_768
  = coe d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.Word.Word64.mod∸half≡half
d_mod'8760'half'8801'half_770 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_770 = erased
-- Once.Word.Word64.mod≡half+half
d_mod'8801'half'43'half_772 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_772 = erased
-- Once.Word.Word64.negOne
d_negOne_774 :: Integer
d_negOne_774 = coe d_negOne_78 (coe (64 :: Integer))
-- Once.Word.Word64.negOne<modulus
d_negOne'60'modulus_776 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_776 v0 v1
  = coe du_negOne'60'modulus_382 (coe (64 :: Integer))
-- Once.Word.Word64.negOne≢0
d_negOne'8802'0_778 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_778 = erased
-- Once.Word.Word64.norm
d_norm_780 :: Integer -> Integer
d_norm_780 = coe d_norm_16 (coe (64 :: Integer))
-- Once.Word.Word64.norm-0
d_norm'45'0_782 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_782 = erased
-- Once.Word.Word64.norm-id
d_norm'45'id_784 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_784 = erased
-- Once.Word.Word64.sdiv2ᵏ
d_sdiv2'7503'_786 :: Integer -> Integer -> Integer
d_sdiv2'7503'_786 = coe d_sdiv2'7503'_138 (coe (64 :: Integer))
-- Once.Word.Word64.shlᵂ
d_shl'7490'_788 :: Integer -> Integer -> Integer
d_shl'7490'_788 = coe d_shl'7490'_132 (coe (64 :: Integer))
-- Once.Word.Word64.sucNegOne≡mod
d_sucNegOne'8801'mod_790 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_790 = erased
-- Once.Word.Word64.tdiv-neg1
d_tdiv'45'neg1_792 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_792 = erased
-- Once.Word.Word64.tmod-neg1
d_tmod'45'neg1_794 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_794 = erased
-- Once.Word.Word64.toWord
d_toWord_796 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_796 v0 v1 = coe du_toWord_68 (coe (64 :: Integer)) v0
-- Once.Word.Word64.toWord≡fromℤ
d_toWord'8801'fromℤ_798 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'8801'fromℤ_798 = erased
-- Once.Word.Word64.toℤ
d_toℤ_800 :: Integer -> Integer
d_toℤ_800 = coe d_toℤ_50 (coe (64 :: Integer))
-- Once.Word.Word64.toℤ-negOne
d_toℤ'45'negOne_802 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_802 = erased
-- Once.Word.Word64.≡ᵇ-refl
d_'8801''7495''45'refl_804 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_804 = erased
-- Once.Word.Word64.≡ᵇ0-false
d_'8801''7495'0'45'false_806 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_806 = erased
-- Once.Word.Word64.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_808 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_808 = erased
-- Once.Word.Word64.⊕-neg
d_'8853''45'neg_810 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_810 = erased
-- Once.Word.Word64.⊕-neg-suc
d_'8853''45'neg'45'suc_812 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_812 = erased
-- Once.Word.Word64.⊕-normʳ
d_'8853''45'norm'691'_814 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_814 = erased
-- Once.Word.Word64.⊕≡+
d_'8853''8801''43'_816 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_816 = erased
-- Once.Word.Word64.⊖-normʳ
d_'8854''45'norm'691'_818 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_818 = erased
-- Once.Word.Word64.⊖≡∸
d_'8854''8801''8760'_820 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_820 = erased
-- Once.Word.Word64.⊗-pow2
d_'8855''45'pow2_822 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_822 = erased
-- Once.Word.Word64.⊝_
d_'8861'__824 :: Integer -> Integer
d_'8861'__824 = coe d_'8861'__44 (coe (64 :: Integer))
-- Once.Word.Word64.⊝-intMin
d_'8861''45'intMin_826 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_826 = erased
