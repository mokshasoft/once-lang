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
import qualified MAlonzo.Code.Once.Spec.Word

-- Once.Word.WidthLaws._._%ˢ_
d__'37''738'__10 :: Integer -> Integer -> Integer -> Integer
d__'37''738'__10 v0
  = coe MAlonzo.Code.Once.Spec.Word.d__'37''738'__122 (coe v0)
-- Once.Word.WidthLaws._._/ˢ_
d__'47''738'__12 :: Integer -> Integer -> Integer -> Integer
d__'47''738'__12 v0
  = coe MAlonzo.Code.Once.Spec.Word.d__'47''738'__116 (coe v0)
-- Once.Word.WidthLaws._._⊕_
d__'8853'__22 :: Integer -> Integer -> Integer -> Integer
d__'8853'__22 v0
  = coe MAlonzo.Code.Once.Spec.Word.d__'8853'__28 (coe v0)
-- Once.Word.WidthLaws._._⊖_
d__'8854'__24 :: Integer -> Integer -> Integer -> Integer
d__'8854'__24 v0
  = coe MAlonzo.Code.Once.Spec.Word.d__'8854'__34 (coe v0)
-- Once.Word.WidthLaws._._⊗_
d__'8855'__26 :: Integer -> Integer -> Integer -> Integer
d__'8855'__26 v0
  = coe MAlonzo.Code.Once.Spec.Word.d__'8855'__40 (coe v0)
-- Once.Word.WidthLaws._.InRange
d_InRange_28 :: Integer -> Integer -> ()
d_InRange_28 = erased
-- Once.Word.WidthLaws._.Word
d_Word_30 :: Integer -> ()
d_Word_30 = erased
-- Once.Word.WidthLaws._.fromℤ
d_fromℤ_32 :: Integer -> Integer -> Integer
d_fromℤ_32 v0 = coe MAlonzo.Code.Once.Spec.Word.d_fromℤ_22 (coe v0)
-- Once.Word.WidthLaws._.half
d_half_34 :: Integer -> Integer
d_half_34 v0 = coe MAlonzo.Code.Once.Spec.Word.d_half_50 (coe v0)
-- Once.Word.WidthLaws._.intMin
d_intMin_38 :: Integer -> Integer
d_intMin_38 v0
  = coe MAlonzo.Code.Once.Spec.Word.d_intMin_56 (coe v0)
-- Once.Word.WidthLaws._.modulus
d_modulus_40 :: Integer -> Integer
d_modulus_40 v0
  = coe MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe v0)
-- Once.Word.WidthLaws._.modulus≢0
d_modulus'8802'0_42 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_42 v0
  = coe MAlonzo.Code.Once.Spec.Word.d_modulus'8802'0_14 (coe v0)
-- Once.Word.WidthLaws._.negOne
d_negOne_44 :: Integer -> Integer
d_negOne_44 v0
  = coe MAlonzo.Code.Once.Spec.Word.d_negOne_58 (coe v0)
-- Once.Word.WidthLaws._.norm
d_norm_46 :: Integer -> Integer -> Integer
d_norm_46 v0 = coe MAlonzo.Code.Once.Spec.Word.d_norm_18 (coe v0)
-- Once.Word.WidthLaws._.tdivℤ
d_tdivℤ_48 :: Integer -> Integer -> Integer -> Integer
d_tdivℤ_48 ~v0 = du_tdivℤ_48
du_tdivℤ_48 :: Integer -> Integer -> Integer
du_tdivℤ_48 = coe MAlonzo.Code.Once.Spec.Word.du_tdivℤ_104
-- Once.Word.WidthLaws._.tmodℤ
d_tmodℤ_50 :: Integer -> Integer -> Integer -> Integer
d_tmodℤ_50 ~v0 = du_tmodℤ_50
du_tmodℤ_50 :: Integer -> Integer -> Integer
du_tmodℤ_50 = coe MAlonzo.Code.Once.Spec.Word.du_tmodℤ_106
-- Once.Word.WidthLaws._.toWord
d_toWord_52 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_52 v0 v1 v2
  = coe MAlonzo.Code.Once.Spec.Word.du_toWord_72 (coe v0) v1
-- Once.Word.WidthLaws._.toℤ
d_toℤ_54 :: Integer -> Integer -> Integer
d_toℤ_54 v0 = coe MAlonzo.Code.Once.Spec.Word.d_toℤ_52 (coe v0)
-- Once.Word.WidthLaws._.⊝_
d_'8861'__56 :: Integer -> Integer -> Integer
d_'8861'__56 v0
  = coe MAlonzo.Code.Once.Spec.Word.d_'8861'__46 (coe v0)
-- Once.Word.WidthLaws.toWord≡fromℤ
d_toWord'8801'fromℤ_62 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'8801'fromℤ_62 = erased
-- Once.Word.WidthLaws.shlᵂ
d_shl'7490'_64 :: Integer -> Integer -> Integer -> Integer
d_shl'7490'_64 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Word.d_norm_18 (coe v0)
      (coe
         mulInt (coe v1)
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe v2)))
-- Once.Word.WidthLaws.sdiv2ᵏ
d_sdiv2'7503'_70 :: Integer -> Integer -> Integer -> Integer
d_sdiv2'7503'_70 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'47''738'__116 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Spec.Word.d_fromℤ_22 (coe v0)
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe v2)))
-- Once.Word.WidthLaws.⊗-pow2
d_'8855''45'pow2_80 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_80 = erased
-- Once.Word.WidthLaws./ˢ-pow2
d_'47''738''45'pow2_92 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_92 = erased
-- Once.Word.WidthLaws.0<modulus
d_0'60'modulus_98 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_98 ~v0 = du_0'60'modulus_98
du_0'60'modulus_98 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'modulus_98
  = coe MAlonzo.Code.Data.Nat.Properties.du_m'94'n'62'0_4482
-- Once.Word.WidthLaws.0<half
d_0'60'half_100 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_100 ~v0 = du_0'60'half_100
du_0'60'half_100 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'half_100
  = coe MAlonzo.Code.Data.Nat.Properties.du_m'94'n'62'0_4482
-- Once.Word.WidthLaws.fromℤ-0
d_fromℤ'45'0_102 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_102 = erased
-- Once.Word.WidthLaws.fromℤ-in-range
d_fromℤ'45'in'45'range_106 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_106 v0 v1
  = case coe v1 of
      _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
          coe
            MAlonzo.Code.Data.Nat.DivMod.du_m'37'n'60'n_166 (coe v1)
            (coe MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe v0))
      _ -> coe
             MAlonzo.Code.Data.Nat.DivMod.du_m'37'n'60'n_166
             (coe
                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                (MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe v0))
                (MAlonzo.Code.Once.Spec.Word.d_norm_18
                   (coe v0) (coe subInt (coe (0 :: Integer)) (coe v1))))
             (coe MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe v0))
-- Once.Word.WidthLaws.⊝-invol-norm
d_'8861''45'invol'45'norm_114 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'invol'45'norm_114 = erased
-- Once.Word.WidthLaws._.b<mod
d_b'60'mod_126 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_b'60'mod_126 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'691''45''60'_5276
      (coe MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe v0))
      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998 (coe v2))
-- Once.Word.WidthLaws.⊝-fromℤ
d_'8861''45'fromℤ_132 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'fromℤ_132 = erased
-- Once.Word.WidthLaws./ˢ-zero
d_'47''738''45'zero_142 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_142 = erased
-- Once.Word.WidthLaws.%ˢ-zero
d_'37''738''45'zero_148 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_148 = erased
-- Once.Word.WidthLaws.≡ᵇ0-false
d_'8801''7495'0'45'false_154 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_154 = erased
-- Once.Word.WidthLaws.<⇒<ᵇtrue
d_'60''8658''60''7495'true_160 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8658''60''7495'true_160 = erased
-- Once.Word.WidthLaws.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_188 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_188 = erased
-- Once.Word.WidthLaws./ˢ-else
d_'47''738''45'else_218 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_218 = erased
-- Once.Word.WidthLaws./ˢ-mid
d_'47''738''45'mid_240 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_240 = erased
-- Once.Word.WidthLaws.%ˢ-else
d_'37''738''45'else_262 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_262 = erased
-- Once.Word.WidthLaws.%ˢ-mid
d_'37''738''45'mid_284 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_284 = erased
-- Once.Word.WidthLaws.tdiv-neg1
d_tdiv'45'neg1_304 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_304 = erased
-- Once.Word.WidthLaws.tmod-neg1
d_tmod'45'neg1_316 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_316 = erased
-- Once.Word.WidthLaws._.half≡2^b
d_half'8801'2'94'b_330 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_330 = erased
-- Once.Word.WidthLaws._.2*n≡n+n
d_2'42'n'8801'n'43'n_336 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_336 = erased
-- Once.Word.WidthLaws._.mod≡half+half
d_mod'8801'half'43'half_342 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_342 = erased
-- Once.Word.WidthLaws._.2≤modulus
d_2'8804'modulus_348 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_348 v0 ~v1 ~v2 = du_2'8804'modulus_348 v0
du_2'8804'modulus_348 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_2'8804'modulus_348 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'45''8804'_3672
      (coe MAlonzo.Code.Once.Spec.Word.d_half_50 (coe v0))
      (coe du_0'60'half_100) (coe du_0'60'half_100)
-- Once.Word.WidthLaws._.0<negOne
d_0'60'negOne_352 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_352 v0 ~v1 ~v2 = du_0'60'negOne_352 v0
du_0'60'negOne_352 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'negOne_352 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'737''45''8804'_5232
      (coe (2 :: Integer))
      (coe MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe v0))
      (coe (1 :: Integer)) (coe du_2'8804'modulus_348 (coe v0))
-- Once.Word.WidthLaws._.negOne≢0
d_negOne'8802'0_354 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_354 = erased
-- Once.Word.WidthLaws._.half<modulus
d_half'60'modulus_356 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_356 v0 ~v1 ~v2 = du_half'60'modulus_356 v0
du_half'60'modulus_356 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_half'60'modulus_356 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3714
      (coe MAlonzo.Code.Once.Spec.Word.d_half_50 (coe v0))
      (coe du_0'60'half_100)
-- Once.Word.WidthLaws._.sucNegOne≡mod
d_sucNegOne'8801'mod_362 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_362 = erased
-- Once.Word.WidthLaws._.negOne<modulus
d_negOne'60'modulus_364 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_364 v0 ~v1 ~v2 = du_negOne'60'modulus_364 v0
du_negOne'60'modulus_364 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_negOne'60'modulus_364 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.Spec.Word.d_negOne_58 (coe v0)))
-- Once.Word.WidthLaws._.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_368 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_368 = erased
-- Once.Word.WidthLaws._.mod∸half≡half
d_mod'8760'half'8801'half_370 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_370 = erased
-- Once.Word.WidthLaws._.⊝-intMin
d_'8861''45'intMin_374 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_374 = erased
-- Once.Word.WidthLaws._.half≤negOne
d_half'8804'negOne_376 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_376 v0 ~v1 ~v2 = du_half'8804'negOne_376 v0
du_half'8804'negOne_376 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_half'8804'negOne_376 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'737''45''8804'_5232
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.Spec.Word.d_half_50 (coe v0)))
      (coe
         addInt (coe MAlonzo.Code.Once.Spec.Word.d_half_50 (coe v0))
         (coe MAlonzo.Code.Once.Spec.Word.d_half_50 (coe v0)))
      (coe (1 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         (MAlonzo.Code.Once.Spec.Word.d_half_50 (coe v0)) (1 :: Integer)
         (MAlonzo.Code.Once.Spec.Word.d_half_50 (coe v0))
         (coe du_0'60'half_100))
-- Once.Word.WidthLaws._.toℤ-negOne
d_toℤ'45'negOne_382 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_382 = erased
-- Once.Word.WidthLaws._.fromℤ-neg1
d_fromℤ'45'neg1_390 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_390 = erased
-- Once.Word.WidthLaws._.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_396 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_396 = erased
-- Once.Word.WidthLaws._._.toℤ-x-hi
d_toℤ'45'x'45'hi_422 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'x'45'hi_422 = erased
-- Once.Word.WidthLaws._.%ˢ-negOne
d_'37''738''45'negOne_428 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_428 = erased
-- Once.Word.WidthLaws._._.tmod-toℤ-negOne
d_tmod'45'toℤ'45'negOne_452 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'toℤ'45'negOne_452 = erased
-- Once.Word.WidthLaws._./ˢ-negOne
d_'47''738''45'negOne_456 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_456 = erased
-- Once.Word.WidthLaws._._.x≡intMin
d_x'8801'intMin_484 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x'8801'intMin_484 = erased
-- Once.Word.WidthLaws._./ˢ-in-range
d_'47''738''45'in'45'range_496 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_496 v0 ~v1 ~v2 v3 v4
  = du_'47''738''45'in'45'range_496 v0 v3 v4
du_'47''738''45'in'45'range_496 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'47''738''45'in'45'range_496 v0 v1 v2
  = let v3 = eqInt (coe v2) (coe (0 :: Integer)) in
    coe
      (if coe v3
         then coe du_negOne'60'modulus_364 (coe v0)
         else (let v4
                     = MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                         (coe
                            eqInt (coe v1)
                            (coe MAlonzo.Code.Once.Spec.Word.d_intMin_56 (coe v0)))
                         (coe
                            eqInt (coe v2)
                            (coe MAlonzo.Code.Once.Spec.Word.d_negOne_58 (coe v0))) in
               coe
                 (if coe v4
                    then coe du_half'60'modulus_356 (coe v0)
                    else coe
                           d_fromℤ'45'in'45'range_106 (coe v0)
                           (coe
                              MAlonzo.Code.Once.Spec.Word.du_tdivℤ_104
                              (coe MAlonzo.Code.Once.Spec.Word.d_toℤ_52 (coe v0) (coe v1))
                              (coe MAlonzo.Code.Once.Spec.Word.d_toℤ_52 (coe v0) (coe v2))))))
-- Once.Word.WidthLaws._.%ˢ-in-range
d_'37''738''45'in'45'range_530 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_530 v0 ~v1 ~v2 v3 v4 v5
  = du_'37''738''45'in'45'range_530 v0 v3 v4 v5
du_'37''738''45'in'45'range_530 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'37''738''45'in'45'range_530 v0 v1 v2 v3
  = let v4 = eqInt (coe v2) (coe (0 :: Integer)) in
    coe
      (if coe v4
         then coe v3
         else (let v5
                     = MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                         (coe
                            eqInt (coe v1)
                            (coe MAlonzo.Code.Once.Spec.Word.d_intMin_56 (coe v0)))
                         (coe
                            eqInt (coe v2)
                            (coe MAlonzo.Code.Once.Spec.Word.d_negOne_58 (coe v0))) in
               coe
                 (if coe v5
                    then coe du_0'60'modulus_98
                    else coe
                           d_fromℤ'45'in'45'range_106 (coe v0)
                           (coe
                              MAlonzo.Code.Once.Spec.Word.du_tmodℤ_106
                              (coe MAlonzo.Code.Once.Spec.Word.d_toℤ_52 (coe v0) (coe v1))
                              (coe MAlonzo.Code.Once.Spec.Word.d_toℤ_52 (coe v0) (coe v2))))))
-- Once.Word.WidthLaws._.unplus
d_unplus_574 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_unplus_574 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_unplus_574 v5
du_unplus_574 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_unplus_574 v0
  = case coe v0 of
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Word.WidthLaws._.lit-hi
d_lit'45'hi_580 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'hi_580 ~v0 ~v1 ~v2 ~v3 v4 = du_lit'45'hi_580 v4
du_lit'45'hi_580 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lit'45'hi_580 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'45''8804'_3672
      (coe (1 :: Integer)) (coe du_unplus_574 (coe v0))
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe (1 :: Integer)))
-- Once.Word.WidthLaws._.lit-lo
d_lit'45'lo_592 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'lo_592 v0 ~v1 ~v2 v3 v4 = du_lit'45'lo_592 v0 v3 v4
du_lit'45'lo_592 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lit'45'lo_592 v0 v1 v2
  = coe
      du_unplus_574
      (coe
         MAlonzo.Code.Data.Integer.Properties.d_neg'45'cancel'45''8804'_3386
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 (1 :: Integer)))
         (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v2))
-- Once.Word.WidthLaws._.toℤ∘fromℤ
d_toℤ'8728'fromℤ_600 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'8728'fromℤ_600 = erased
-- Once.Word.WidthLaws._._.n<half
d_n'60'half_610 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'60'half_610 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_n'60'half_610 v5
du_n'60'half_610 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n'60'half_610 v0 = coe du_lit'45'hi_580 (coe v0)
-- Once.Word.WidthLaws._._.n<mod
d_n'60'mod_612 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'60'mod_612 v0 ~v1 ~v2 ~v3 ~v4 v5 = du_n'60'mod_612 v0 v5
du_n'60'mod_612 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n'60'mod_612 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
         (coe du_n'60'half_610 (coe v1)))
      (coe du_half'60'modulus_356 (coe v0))
-- Once.Word.WidthLaws._._.norm-n
d_norm'45'n_614 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'n_614 = erased
-- Once.Word.WidthLaws._._.guard
d_guard_616 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_guard_616 = erased
-- Once.Word.WidthLaws._._.sn≤half
d_sn'8804'half_630 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sn'8804'half_630 v0 ~v1 ~v2 v3 v4 ~v5
  = du_sn'8804'half_630 v0 v3 v4
du_sn'8804'half_630 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sn'8804'half_630 v0 v1 v2
  = coe du_lit'45'lo_592 (coe v0) (coe v1) (coe v2)
-- Once.Word.WidthLaws._._.sn<mod
d_sn'60'mod_632 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sn'60'mod_632 v0 ~v1 ~v2 v3 v4 ~v5 = du_sn'60'mod_632 v0 v3 v4
du_sn'60'mod_632 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sn'60'mod_632 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
      (coe du_sn'8804'half_630 (coe v0) (coe v1) (coe v2))
      (coe du_half'60'modulus_356 (coe v0))
-- Once.Word.WidthLaws._._.w
d_w_634 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 -> Integer
d_w_634 v0 ~v1 ~v2 v3 ~v4 ~v5 = du_w_634 v0 v3
du_w_634 :: Integer -> Integer -> Integer
du_w_634 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
      (MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe v0))
      (addInt (coe (1 :: Integer)) (coe v1))
-- Once.Word.WidthLaws._._.word
d_word_636 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_word_636 = erased
-- Once.Word.WidthLaws._._._.w<mod
d_w'60'mod_642 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_w'60'mod_642 v0 ~v1 ~v2 v3 v4 ~v5 = du_w'60'mod_642 v0 v3 v4
du_w'60'mod_642 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_w'60'mod_642 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'691''45''60'_5276
      (coe MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe v0))
      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
         (coe du_sn'60'mod_632 (coe v0) (coe v1) (coe v2)))
-- Once.Word.WidthLaws._._.half≤w
d_half'8804'w_646 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'w_646 v0 ~v1 ~v2 v3 v4 ~v5
  = du_half'8804'w_646 v0 v3 v4
du_half'8804'w_646 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_half'8804'w_646 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'691''45''8804'_5240
      (coe addInt (coe (1 :: Integer)) (coe v1))
      (coe MAlonzo.Code.Once.Spec.Word.d_half_50 (coe v0))
      (coe MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe v0))
      (coe du_sn'8804'half_630 (coe v0) (coe v1) (coe v2))
-- Once.Word.WidthLaws._._.w<mod
d_w'60'mod_650 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_w'60'mod_650 v0 ~v1 ~v2 v3 v4 ~v5 = du_w'60'mod_650 v0 v3 v4
du_w'60'mod_650 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_w'60'mod_650 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'691''45''60'_5276
      (coe MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe v0))
      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
         (coe du_sn'60'mod_632 (coe v0) (coe v1) (coe v2)))
-- Once.Word.WidthLaws._._.signed
d_signed_652 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_signed_652 = erased
-- Once.Word.WidthLaws.⊕≡+
d_'8853''8801''43'_664 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_664 = erased
-- Once.Word.WidthLaws.⊖≡∸
d_'8854''8801''8760'_676 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_676 = erased
-- Once.Word.WidthLaws._.y≤mod
d_y'8804'mod_690 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_y'8804'mod_690 ~v0 ~v1 ~v2 v3 v4 = du_y'8804'mod_690 v3 v4
du_y'8804'mod_690 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_y'8804'mod_690 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998 (coe v1))
-- Once.Word.WidthLaws.⊕-normʳ
d_'8853''45'norm'691'_696 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_696 = erased
-- Once.Word.WidthLaws.⊖-normʳ
d_'8854''45'norm'691'_708 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_708 = erased
-- Once.Word.WidthLaws.norm-id
d_norm'45'id_720 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_720 = erased
-- Once.Word.WidthLaws.1<modulus
d_1'60'modulus_722 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_722 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'94''45'mono'691''45''8804'_4502
      (coe (2 :: Integer)) (coe (1 :: Integer)) (coe v0) (coe v1)
-- Once.Word.WidthLaws.norm-0
d_norm'45'0_726 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_726 = erased
-- Once.Word.WidthLaws.⊕-neg-suc
d_'8853''45'neg'45'suc_732 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_732 = erased
-- Once.Word.WidthLaws.⊕-neg
d_'8853''45'neg_746 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_746 = erased
-- Once.Word.WidthLaws.norm-+ˡ
d_norm'45''43''737'_764 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45''43''737'_764 = erased
-- Once.Word.WidthLaws.⊕⊖-cancel
d_'8853''8854''45'cancel_776 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8854''45'cancel_776 = erased
-- Once.Word.WidthLaws.⊕⊖-norm
d_'8853''8854''45'norm_792 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8854''45'norm_792 = erased
-- Once.Word.WidthLaws.⊖-self
d_'8854''45'self_802 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'self_802 = erased
-- Once.Word.WidthLaws.sbb-zero
d_sbb'45'zero_808 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sbb'45'zero_808 = erased
-- Once.Word.WidthLaws.sbb-pos
d_sbb'45'pos_820 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sbb'45'pos_820 = erased
