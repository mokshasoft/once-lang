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
-- Once.Word.Width.⊝-invol-norm
d_'8861''45'invol'45'norm_182 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'invol'45'norm_182 = erased
-- Once.Word.Width._.b<mod
d_b'60'mod_194 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_b'60'mod_194 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'691''45''60'_5276
      (coe d_modulus_10 (coe v0))
      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998 (coe v2))
-- Once.Word.Width.⊝-fromℤ
d_'8861''45'fromℤ_200 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'fromℤ_200 = erased
-- Once.Word.Width./ˢ-zero
d_'47''738''45'zero_210 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_210 = erased
-- Once.Word.Width.%ˢ-zero
d_'37''738''45'zero_216 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_216 = erased
-- Once.Word.Width.≡ᵇ-refl
d_'8801''7495''45'refl_222 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_222 = erased
-- Once.Word.Width.≡ᵇ0-false
d_'8801''7495'0'45'false_228 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_228 = erased
-- Once.Word.Width.<⇒<ᵇtrue
d_'60''8658''60''7495'true_234 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8658''60''7495'true_234 = erased
-- Once.Word.Width.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_262 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_262 = erased
-- Once.Word.Width./ˢ-else
d_'47''738''45'else_292 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_292 = erased
-- Once.Word.Width./ˢ-mid
d_'47''738''45'mid_314 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_314 = erased
-- Once.Word.Width.%ˢ-else
d_'37''738''45'else_336 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_336 = erased
-- Once.Word.Width.%ˢ-mid
d_'37''738''45'mid_358 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_358 = erased
-- Once.Word.Width.tdiv-neg1
d_tdiv'45'neg1_378 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_378 = erased
-- Once.Word.Width.tmod-neg1
d_tmod'45'neg1_390 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_390 = erased
-- Once.Word.Width._.half≡2^b
d_half'8801'2'94'b_404 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_404 = erased
-- Once.Word.Width._.2*n≡n+n
d_2'42'n'8801'n'43'n_410 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_410 = erased
-- Once.Word.Width._.mod≡half+half
d_mod'8801'half'43'half_416 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_416 = erased
-- Once.Word.Width._.2≤modulus
d_2'8804'modulus_422 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_422 v0 ~v1 ~v2 = du_2'8804'modulus_422 v0
du_2'8804'modulus_422 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_2'8804'modulus_422 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'45''8804'_3672
      (coe d_half_48 (coe v0)) (coe du_0'60'half_168)
      (coe du_0'60'half_168)
-- Once.Word.Width._.0<negOne
d_0'60'negOne_426 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_426 v0 ~v1 ~v2 = du_0'60'negOne_426 v0
du_0'60'negOne_426 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'negOne_426 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'737''45''8804'_5232
      (coe (2 :: Integer)) (coe d_modulus_10 (coe v0))
      (coe (1 :: Integer)) (coe du_2'8804'modulus_422 (coe v0))
-- Once.Word.Width._.negOne≢0
d_negOne'8802'0_428 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_428 = erased
-- Once.Word.Width._.half<modulus
d_half'60'modulus_430 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_430 v0 ~v1 ~v2 = du_half'60'modulus_430 v0
du_half'60'modulus_430 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_half'60'modulus_430 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3714
      (coe d_half_48 (coe v0)) (coe du_0'60'half_168)
-- Once.Word.Width._.sucNegOne≡mod
d_sucNegOne'8801'mod_436 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_436 = erased
-- Once.Word.Width._.negOne<modulus
d_negOne'60'modulus_438 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_438 v0 ~v1 ~v2 = du_negOne'60'modulus_438 v0
du_negOne'60'modulus_438 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_negOne'60'modulus_438 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe addInt (coe (1 :: Integer)) (coe d_negOne_78 (coe v0)))
-- Once.Word.Width._.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_442 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_442 = erased
-- Once.Word.Width._.mod∸half≡half
d_mod'8760'half'8801'half_444 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_444 = erased
-- Once.Word.Width._.⊝-intMin
d_'8861''45'intMin_448 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_448 = erased
-- Once.Word.Width._.half≤negOne
d_half'8804'negOne_450 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_450 v0 ~v1 ~v2 = du_half'8804'negOne_450 v0
du_half'8804'negOne_450 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_half'8804'negOne_450 v0
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
d_toℤ'45'negOne_456 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_456 = erased
-- Once.Word.Width._.fromℤ-neg1
d_fromℤ'45'neg1_464 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_464 = erased
-- Once.Word.Width._.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_470 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_470 = erased
-- Once.Word.Width._._.toℤ-x-hi
d_toℤ'45'x'45'hi_496 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'x'45'hi_496 = erased
-- Once.Word.Width._.%ˢ-negOne
d_'37''738''45'negOne_502 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_502 = erased
-- Once.Word.Width._._.tmod-toℤ-negOne
d_tmod'45'toℤ'45'negOne_526 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'toℤ'45'negOne_526 = erased
-- Once.Word.Width._./ˢ-negOne
d_'47''738''45'negOne_530 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_530 = erased
-- Once.Word.Width._._.x≡intMin
d_x'8801'intMin_558 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x'8801'intMin_558 = erased
-- Once.Word.Width._./ˢ-in-range
d_'47''738''45'in'45'range_570 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_570 v0 ~v1 ~v2 v3 v4
  = du_'47''738''45'in'45'range_570 v0 v3 v4
du_'47''738''45'in'45'range_570 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'47''738''45'in'45'range_570 v0 v1 v2
  = let v3 = eqInt (coe v2) (coe (0 :: Integer)) in
    coe
      (if coe v3
         then coe du_negOne'60'modulus_438 (coe v0)
         else (let v4
                     = MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                         (coe eqInt (coe v1) (coe d_intMin_54 (coe v0)))
                         (coe eqInt (coe v2) (coe d_negOne_78 (coe v0))) in
               coe
                 (if coe v4
                    then coe du_half'60'modulus_430 (coe v0)
                    else coe
                           d_fromℤ'45'in'45'range_174 (coe v0)
                           (coe
                              du_tdivℤ_108 (coe d_toℤ_50 (coe v0) (coe v1))
                              (coe d_toℤ_50 (coe v0) (coe v2))))))
-- Once.Word.Width._.%ˢ-in-range
d_'37''738''45'in'45'range_604 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_604 v0 ~v1 ~v2 v3 v4 v5
  = du_'37''738''45'in'45'range_604 v0 v3 v4 v5
du_'37''738''45'in'45'range_604 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'37''738''45'in'45'range_604 v0 v1 v2 v3
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
-- Once.Word.Width._.unplus
d_unplus_648 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_unplus_648 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_unplus_648 v5
du_unplus_648 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_unplus_648 v0
  = case coe v0 of
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Word.Width._.lit-hi
d_lit'45'hi_654 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'hi_654 ~v0 ~v1 ~v2 ~v3 v4 = du_lit'45'hi_654 v4
du_lit'45'hi_654 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lit'45'hi_654 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'45''8804'_3672
      (coe (1 :: Integer)) (coe du_unplus_648 (coe v0))
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe (1 :: Integer)))
-- Once.Word.Width._.lit-lo
d_lit'45'lo_666 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'lo_666 v0 ~v1 ~v2 v3 v4 = du_lit'45'lo_666 v0 v3 v4
du_lit'45'lo_666 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lit'45'lo_666 v0 v1 v2
  = coe
      du_unplus_648
      (coe
         MAlonzo.Code.Data.Integer.Properties.d_neg'45'cancel'45''8804'_3386
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 (1 :: Integer)))
         (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v2))
-- Once.Word.Width._.toℤ∘fromℤ
d_toℤ'8728'fromℤ_674 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'8728'fromℤ_674 = erased
-- Once.Word.Width._._.n<half
d_n'60'half_684 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'60'half_684 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_n'60'half_684 v5
du_n'60'half_684 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n'60'half_684 v0 = coe du_lit'45'hi_654 (coe v0)
-- Once.Word.Width._._.n<mod
d_n'60'mod_686 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'60'mod_686 v0 ~v1 ~v2 ~v3 ~v4 v5 = du_n'60'mod_686 v0 v5
du_n'60'mod_686 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n'60'mod_686 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
         (coe du_n'60'half_684 (coe v1)))
      (coe du_half'60'modulus_430 (coe v0))
-- Once.Word.Width._._.norm-n
d_norm'45'n_688 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'n_688 = erased
-- Once.Word.Width._._.guard
d_guard_690 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_guard_690 = erased
-- Once.Word.Width._._.sn≤half
d_sn'8804'half_704 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sn'8804'half_704 v0 ~v1 ~v2 v3 v4 ~v5
  = du_sn'8804'half_704 v0 v3 v4
du_sn'8804'half_704 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sn'8804'half_704 v0 v1 v2
  = coe du_lit'45'lo_666 (coe v0) (coe v1) (coe v2)
-- Once.Word.Width._._.sn<mod
d_sn'60'mod_706 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sn'60'mod_706 v0 ~v1 ~v2 v3 v4 ~v5 = du_sn'60'mod_706 v0 v3 v4
du_sn'60'mod_706 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sn'60'mod_706 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
      (coe du_sn'8804'half_704 (coe v0) (coe v1) (coe v2))
      (coe du_half'60'modulus_430 (coe v0))
-- Once.Word.Width._._.w
d_w_708 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 -> Integer
d_w_708 v0 ~v1 ~v2 v3 ~v4 ~v5 = du_w_708 v0 v3
du_w_708 :: Integer -> Integer -> Integer
du_w_708 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_modulus_10 (coe v0))
      (addInt (coe (1 :: Integer)) (coe v1))
-- Once.Word.Width._._.word
d_word_710 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_word_710 = erased
-- Once.Word.Width._._._.w<mod
d_w'60'mod_716 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_w'60'mod_716 v0 ~v1 ~v2 v3 v4 ~v5 = du_w'60'mod_716 v0 v3 v4
du_w'60'mod_716 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_w'60'mod_716 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'691''45''60'_5276
      (coe d_modulus_10 (coe v0))
      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
         (coe du_sn'60'mod_706 (coe v0) (coe v1) (coe v2)))
-- Once.Word.Width._._.half≤w
d_half'8804'w_720 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'w_720 v0 ~v1 ~v2 v3 v4 ~v5
  = du_half'8804'w_720 v0 v3 v4
du_half'8804'w_720 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_half'8804'w_720 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'691''45''8804'_5240
      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe d_half_48 (coe v0))
      (coe d_modulus_10 (coe v0))
      (coe du_sn'8804'half_704 (coe v0) (coe v1) (coe v2))
-- Once.Word.Width._._.w<mod
d_w'60'mod_724 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_w'60'mod_724 v0 ~v1 ~v2 v3 v4 ~v5 = du_w'60'mod_724 v0 v3 v4
du_w'60'mod_724 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_w'60'mod_724 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'691''45''60'_5276
      (coe d_modulus_10 (coe v0))
      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
         (coe du_sn'60'mod_706 (coe v0) (coe v1) (coe v2)))
-- Once.Word.Width._._.signed
d_signed_726 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_signed_726 = erased
-- Once.Word.Width.⊕≡+
d_'8853''8801''43'_738 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_738 = erased
-- Once.Word.Width.⊖≡∸
d_'8854''8801''8760'_750 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_750 = erased
-- Once.Word.Width._.y≤mod
d_y'8804'mod_764 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_y'8804'mod_764 ~v0 ~v1 ~v2 v3 v4 = du_y'8804'mod_764 v3 v4
du_y'8804'mod_764 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_y'8804'mod_764 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998 (coe v1))
-- Once.Word.Width.⊕-normʳ
d_'8853''45'norm'691'_770 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_770 = erased
-- Once.Word.Width.⊖-normʳ
d_'8854''45'norm'691'_782 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_782 = erased
-- Once.Word.Width.norm-id
d_norm'45'id_794 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_794 = erased
-- Once.Word.Width.1<modulus
d_1'60'modulus_796 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_796 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'94''45'mono'691''45''8804'_4502
      (coe (2 :: Integer)) (coe (1 :: Integer)) (coe v0) (coe v1)
-- Once.Word.Width.norm-0
d_norm'45'0_800 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_800 = erased
-- Once.Word.Width.⊕-neg-suc
d_'8853''45'neg'45'suc_806 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_806 = erased
-- Once.Word.Width.⊕-neg
d_'8853''45'neg_820 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_820 = erased
-- Once.Word.Word64._%ˢ_
d__'37''738'__836 :: Integer -> Integer -> Integer
d__'37''738'__836 = coe d__'37''738'__126 (coe (64 :: Integer))
-- Once.Word.Word64._/ˢ_
d__'47''738'__838 :: Integer -> Integer -> Integer
d__'47''738'__838 = coe d__'47''738'__120 (coe (64 :: Integer))
-- Once.Word.Word64._<ˢ_
d__'60''738'__840 :: Integer -> Integer -> Bool
d__'60''738'__840 = coe d__'60''738'__80 (coe (64 :: Integer))
-- Once.Word.Word64._≡ʷ_
d__'8801''695'__842 :: Integer -> Integer -> Bool
d__'8801''695'__842 = coe du__'8801''695'__86
-- Once.Word.Word64._⊕_
d__'8853'__844 :: Integer -> Integer -> Integer
d__'8853'__844 = coe d__'8853'__26 (coe (64 :: Integer))
-- Once.Word.Word64._⊖_
d__'8854'__846 :: Integer -> Integer -> Integer
d__'8854'__846 = coe d__'8854'__32 (coe (64 :: Integer))
-- Once.Word.Word64._⊗_
d__'8855'__848 :: Integer -> Integer -> Integer
d__'8855'__848 = coe d__'8855'__38 (coe (64 :: Integer))
-- Once.Word.Word64.%ˢ-else
d_'37''738''45'else_850 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_850 = erased
-- Once.Word.Word64.%ˢ-in-range
d_'37''738''45'in'45'range_852 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_852 v0 v1 v2 v3 v4
  = coe
      du_'37''738''45'in'45'range_604 (coe (64 :: Integer)) v2 v3 v4
-- Once.Word.Word64.%ˢ-mid
d_'37''738''45'mid_854 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_854 = erased
-- Once.Word.Word64.%ˢ-negOne
d_'37''738''45'negOne_856 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_856 = erased
-- Once.Word.Word64.%ˢ-zero
d_'37''738''45'zero_858 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_858 = erased
-- Once.Word.Word64./ˢ-else
d_'47''738''45'else_860 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_860 = erased
-- Once.Word.Word64./ˢ-in-range
d_'47''738''45'in'45'range_862 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_862 v0 v1 v2 v3
  = coe du_'47''738''45'in'45'range_570 (coe (64 :: Integer)) v2 v3
-- Once.Word.Word64./ˢ-mid
d_'47''738''45'mid_864 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_864 = erased
-- Once.Word.Word64./ˢ-negOne
d_'47''738''45'negOne_866 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_866 = erased
-- Once.Word.Word64./ˢ-pow2
d_'47''738''45'pow2_868 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_868 = erased
-- Once.Word.Word64./ˢ-zero
d_'47''738''45'zero_870 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_870 = erased
-- Once.Word.Word64.0<half
d_0'60'half_872 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_872 = coe du_0'60'half_168
-- Once.Word.Word64.0<modulus
d_0'60'modulus_874 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_874 = coe du_0'60'modulus_166
-- Once.Word.Word64.0<negOne
d_0'60'negOne_876 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_876 v0 v1
  = coe du_0'60'negOne_426 (coe (64 :: Integer))
-- Once.Word.Word64.1<modulus
d_1'60'modulus_878 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_878 = coe d_1'60'modulus_796 (coe (64 :: Integer))
-- Once.Word.Word64.2*n≡n+n
d_2'42'n'8801'n'43'n_880 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_880 = erased
-- Once.Word.Word64.2≤modulus
d_2'8804'modulus_882 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_882 v0 v1
  = coe du_2'8804'modulus_422 (coe (64 :: Integer))
-- Once.Word.Word64.<⇒<ᵇtrue
d_'60''8658''60''7495'true_884 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8658''60''7495'true_884 = erased
-- Once.Word.Word64.InRange
d_InRange_886 :: Integer -> ()
d_InRange_886 = erased
-- Once.Word.Word64.Word
d_Word_888 :: ()
d_Word_888 = erased
-- Once.Word.Word64.fromℤ
d_fromℤ_890 :: Integer -> Integer
d_fromℤ_890 = coe d_fromℤ_20 (coe (64 :: Integer))
-- Once.Word.Word64.fromℤ-0
d_fromℤ'45'0_892 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_892 = erased
-- Once.Word.Word64.fromℤ-in-range
d_fromℤ'45'in'45'range_894 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_894
  = coe d_fromℤ'45'in'45'range_174 (coe (64 :: Integer))
-- Once.Word.Word64.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_896 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_896 = erased
-- Once.Word.Word64.fromℤ-neg1
d_fromℤ'45'neg1_898 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_898 = erased
-- Once.Word.Word64.half
d_half_900 :: Integer
d_half_900 = coe d_half_48 (coe (64 :: Integer))
-- Once.Word.Word64.half<modulus
d_half'60'modulus_902 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_902 v0 v1
  = coe du_half'60'modulus_430 (coe (64 :: Integer))
-- Once.Word.Word64.half≡2^b
d_half'8801'2'94'b_904 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_904 = erased
-- Once.Word.Word64.half≤negOne
d_half'8804'negOne_906 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_906 v0 v1
  = coe du_half'8804'negOne_450 (coe (64 :: Integer))
-- Once.Word.Word64.inRange?
d_inRange'63'_908 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_908 = coe d_inRange'63'_62 (coe (64 :: Integer))
-- Once.Word.Word64.intMin
d_intMin_910 :: Integer
d_intMin_910 = coe d_intMin_54 (coe (64 :: Integer))
-- Once.Word.Word64.lit-hi
d_lit'45'hi_912 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'hi_912 v0 v1 v2 v3 = coe du_lit'45'hi_654 v3
-- Once.Word.Word64.lit-lo
d_lit'45'lo_914 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'lo_914 v0 v1 v2 v3
  = coe du_lit'45'lo_666 (coe (64 :: Integer)) v2 v3
-- Once.Word.Word64.modulus
d_modulus_916 :: Integer
d_modulus_916 = coe d_modulus_10 (coe (64 :: Integer))
-- Once.Word.Word64.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_918 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_918 = erased
-- Once.Word.Word64.modulus≢0
d_modulus'8802'0_920 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_920
  = coe d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.Word.Word64.mod∸half≡half
d_mod'8760'half'8801'half_922 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_922 = erased
-- Once.Word.Word64.mod≡half+half
d_mod'8801'half'43'half_924 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_924 = erased
-- Once.Word.Word64.negOne
d_negOne_926 :: Integer
d_negOne_926 = coe d_negOne_78 (coe (64 :: Integer))
-- Once.Word.Word64.negOne<modulus
d_negOne'60'modulus_928 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_928 v0 v1
  = coe du_negOne'60'modulus_438 (coe (64 :: Integer))
-- Once.Word.Word64.negOne≢0
d_negOne'8802'0_930 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_930 = erased
-- Once.Word.Word64.norm
d_norm_932 :: Integer -> Integer
d_norm_932 = coe d_norm_16 (coe (64 :: Integer))
-- Once.Word.Word64.norm-0
d_norm'45'0_934 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_934 = erased
-- Once.Word.Word64.norm-id
d_norm'45'id_936 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_936 = erased
-- Once.Word.Word64.sdiv2ᵏ
d_sdiv2'7503'_938 :: Integer -> Integer -> Integer
d_sdiv2'7503'_938 = coe d_sdiv2'7503'_138 (coe (64 :: Integer))
-- Once.Word.Word64.shlᵂ
d_shl'7490'_940 :: Integer -> Integer -> Integer
d_shl'7490'_940 = coe d_shl'7490'_132 (coe (64 :: Integer))
-- Once.Word.Word64.sucNegOne≡mod
d_sucNegOne'8801'mod_942 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_942 = erased
-- Once.Word.Word64.tdiv-neg1
d_tdiv'45'neg1_944 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_944 = erased
-- Once.Word.Word64.tmod-neg1
d_tmod'45'neg1_946 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_946 = erased
-- Once.Word.Word64.toWord
d_toWord_948 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_948 v0 v1 = coe du_toWord_68 (coe (64 :: Integer)) v0
-- Once.Word.Word64.toWord≡fromℤ
d_toWord'8801'fromℤ_950 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'8801'fromℤ_950 = erased
-- Once.Word.Word64.toℤ
d_toℤ_952 :: Integer -> Integer
d_toℤ_952 = coe d_toℤ_50 (coe (64 :: Integer))
-- Once.Word.Word64.toℤ-negOne
d_toℤ'45'negOne_954 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_954 = erased
-- Once.Word.Word64.toℤ∘fromℤ
d_toℤ'8728'fromℤ_956 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'8728'fromℤ_956 = erased
-- Once.Word.Word64.unplus
d_unplus_958 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_unplus_958 v0 v1 v2 v3 v4 = coe du_unplus_648 v4
-- Once.Word.Word64.≡ᵇ-refl
d_'8801''7495''45'refl_960 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_960 = erased
-- Once.Word.Word64.≡ᵇ0-false
d_'8801''7495'0'45'false_962 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_962 = erased
-- Once.Word.Word64.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_964 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_964 = erased
-- Once.Word.Word64.⊕-neg
d_'8853''45'neg_966 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_966 = erased
-- Once.Word.Word64.⊕-neg-suc
d_'8853''45'neg'45'suc_968 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_968 = erased
-- Once.Word.Word64.⊕-normʳ
d_'8853''45'norm'691'_970 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_970 = erased
-- Once.Word.Word64.⊕≡+
d_'8853''8801''43'_972 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_972 = erased
-- Once.Word.Word64.⊖-normʳ
d_'8854''45'norm'691'_974 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_974 = erased
-- Once.Word.Word64.⊖≡∸
d_'8854''8801''8760'_976 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_976 = erased
-- Once.Word.Word64.⊗-pow2
d_'8855''45'pow2_978 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_978 = erased
-- Once.Word.Word64.⊝_
d_'8861'__980 :: Integer -> Integer
d_'8861'__980 = coe d_'8861'__44 (coe (64 :: Integer))
-- Once.Word.Word64.⊝-fromℤ
d_'8861''45'fromℤ_982 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'fromℤ_982 = erased
-- Once.Word.Word64.⊝-intMin
d_'8861''45'intMin_984 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_984 = erased
-- Once.Word.Word64.⊝-invol-norm
d_'8861''45'invol'45'norm_986 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'invol'45'norm_986 = erased
