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

module MAlonzo.Code.Once.Arith.SigOp.Builders where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Arith.SigOp.Builders.W._%ˢ_
d__'37''738'__10 :: Integer -> Integer -> Integer
d__'37''738'__10
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__104 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W._/ˢ_
d__'47''738'__12 :: Integer -> Integer -> Integer
d__'47''738'__12
  = coe MAlonzo.Code.Once.Word.d__'47''738'__98 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W._<ˢ_
d__'60''738'__14 :: Integer -> Integer -> Bool
d__'60''738'__14
  = coe MAlonzo.Code.Once.Word.d__'60''738'__58 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W._≡ʷ_
d__'8801''695'__16 :: Integer -> Integer -> Bool
d__'8801''695'__16 = coe MAlonzo.Code.Once.Word.du__'8801''695'__64
-- Once.Arith.SigOp.Builders.W._⊕_
d__'8853'__18 :: Integer -> Integer -> Integer
d__'8853'__18
  = coe MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W._⊖_
d__'8854'__20 :: Integer -> Integer -> Integer
d__'8854'__20
  = coe MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W._⊗_
d__'8855'__22 :: Integer -> Integer -> Integer
d__'8855'__22
  = coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.%ˢ-else
d_'37''738''45'else_24 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_24 = erased
-- Once.Arith.SigOp.Builders.W.%ˢ-in-range
d_'37''738''45'in'45'range_26 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_26 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_526
      (coe (64 :: Integer)) v2 v3 v4
-- Once.Arith.SigOp.Builders.W.%ˢ-mid
d_'37''738''45'mid_28 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_28 = erased
-- Once.Arith.SigOp.Builders.W.%ˢ-negOne
d_'37''738''45'negOne_30 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_30 = erased
-- Once.Arith.SigOp.Builders.W.%ˢ-zero
d_'37''738''45'zero_32 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_32 = erased
-- Once.Arith.SigOp.Builders.W./ˢ-else
d_'47''738''45'else_34 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_34 = erased
-- Once.Arith.SigOp.Builders.W./ˢ-in-range
d_'47''738''45'in'45'range_36 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_36 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_492
      (coe (64 :: Integer)) v2 v3
-- Once.Arith.SigOp.Builders.W./ˢ-mid
d_'47''738''45'mid_38 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_38 = erased
-- Once.Arith.SigOp.Builders.W./ˢ-negOne
d_'47''738''45'negOne_40 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_40 = erased
-- Once.Arith.SigOp.Builders.W./ˢ-pow2
d_'47''738''45'pow2_42 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_42 = erased
-- Once.Arith.SigOp.Builders.W./ˢ-zero
d_'47''738''45'zero_44 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_44 = erased
-- Once.Arith.SigOp.Builders.W.0<half
d_0'60'half_46 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_46 = coe MAlonzo.Code.Once.Word.du_0'60'half_146
-- Once.Arith.SigOp.Builders.W.0<modulus
d_0'60'modulus_48 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_48 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_144
-- Once.Arith.SigOp.Builders.W.0<negOne
d_0'60'negOne_50 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_50 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_348 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.1<modulus
d_1'60'modulus_52 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_52
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_628 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.2*n≡n+n
d_2'42'n'8801'n'43'n_54 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_54 = erased
-- Once.Arith.SigOp.Builders.W.2≤modulus
d_2'8804'modulus_56 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_56 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_344 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.Word
d_Word_58 :: ()
d_Word_58 = erased
-- Once.Arith.SigOp.Builders.W.fromℤ
d_fromℤ_60 :: Integer -> Integer
d_fromℤ_60
  = coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.fromℤ-0
d_fromℤ'45'0_62 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_62 = erased
-- Once.Arith.SigOp.Builders.W.fromℤ-in-range
d_fromℤ'45'in'45'range_64 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_64
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_152
      (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_66 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_66 = erased
-- Once.Arith.SigOp.Builders.W.fromℤ-neg1
d_fromℤ'45'neg1_68 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_68 = erased
-- Once.Arith.SigOp.Builders.W.half
d_half_70 :: Integer
d_half_70
  = coe MAlonzo.Code.Once.Word.d_half_48 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.half<modulus
d_half'60'modulus_72 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_72 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_352 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.half≡2^b
d_half'8801'2'94'b_74 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_74 = erased
-- Once.Arith.SigOp.Builders.W.half≤negOne
d_half'8804'negOne_76 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_76 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_372
      (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.intMin
d_intMin_78 :: Integer
d_intMin_78
  = coe MAlonzo.Code.Once.Word.d_intMin_54 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.modulus
d_modulus_80 :: Integer
d_modulus_80
  = coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_82 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_82 = erased
-- Once.Arith.SigOp.Builders.W.modulus≢0
d_modulus'8802'0_84 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_84
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.mod∸half≡half
d_mod'8760'half'8801'half_86 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_86 = erased
-- Once.Arith.SigOp.Builders.W.mod≡half+half
d_mod'8801'half'43'half_88 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_88 = erased
-- Once.Arith.SigOp.Builders.W.negOne
d_negOne_90 :: Integer
d_negOne_90
  = coe MAlonzo.Code.Once.Word.d_negOne_56 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.negOne<modulus
d_negOne'60'modulus_92 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_92 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_360
      (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.negOne≢0
d_negOne'8802'0_94 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_94 = erased
-- Once.Arith.SigOp.Builders.W.norm
d_norm_96 :: Integer -> Integer
d_norm_96
  = coe MAlonzo.Code.Once.Word.d_norm_16 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.norm-0
d_norm'45'0_98 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_98 = erased
-- Once.Arith.SigOp.Builders.W.norm-id
d_norm'45'id_100 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_100 = erased
-- Once.Arith.SigOp.Builders.W.sdiv2ᵏ
d_sdiv2'7503'_102 :: Integer -> Integer -> Integer
d_sdiv2'7503'_102
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_116 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.shlᵂ
d_shl'7490'_104 :: Integer -> Integer -> Integer
d_shl'7490'_104
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_110 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.sucNegOne≡mod
d_sucNegOne'8801'mod_106 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_106 = erased
-- Once.Arith.SigOp.Builders.W.tdiv-neg1
d_tdiv'45'neg1_108 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_108 = erased
-- Once.Arith.SigOp.Builders.W.tmod-neg1
d_tmod'45'neg1_110 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_110 = erased
-- Once.Arith.SigOp.Builders.W.toℤ
d_toℤ_112 :: Integer -> Integer
d_toℤ_112
  = coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.toℤ-negOne
d_toℤ'45'negOne_114 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_114 = erased
-- Once.Arith.SigOp.Builders.W.≡ᵇ-refl
d_'8801''7495''45'refl_116 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_116 = erased
-- Once.Arith.SigOp.Builders.W.≡ᵇ0-false
d_'8801''7495'0'45'false_118 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_118 = erased
-- Once.Arith.SigOp.Builders.W.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_120 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_120 = erased
-- Once.Arith.SigOp.Builders.W.⊕-neg
d_'8853''45'neg_122 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_122 = erased
-- Once.Arith.SigOp.Builders.W.⊕-neg-suc
d_'8853''45'neg'45'suc_124 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_124 = erased
-- Once.Arith.SigOp.Builders.W.⊕-normʳ
d_'8853''45'norm'691'_126 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_126 = erased
-- Once.Arith.SigOp.Builders.W.⊕≡+
d_'8853''8801''43'_128 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_128 = erased
-- Once.Arith.SigOp.Builders.W.⊖-normʳ
d_'8854''45'norm'691'_130 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_130 = erased
-- Once.Arith.SigOp.Builders.W.⊖≡∸
d_'8854''8801''8760'_132 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_132 = erased
-- Once.Arith.SigOp.Builders.W.⊗-pow2
d_'8855''45'pow2_134 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_134 = erased
-- Once.Arith.SigOp.Builders.W.⊝_
d_'8861'__136 :: Integer -> Integer
d_'8861'__136
  = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.⊝-intMin
d_'8861''45'intMin_138 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_138 = erased
-- Once.Arith.SigOp.Builders.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_142 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_142
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'base'45'to'45'full_636
-- Once.Arith.SigOp.Builders.M.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_144 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_144 = erased
-- Once.Arith.SigOp.Builders.M.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_146 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_146 = erased
-- Once.Arith.SigOp.Builders.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_148 ::
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_148
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'full'45'to'45'base_600
-- Once.Arith.SigOp.Builders.M.coerce-functor
d_coerce'45'functor_150 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor_150 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_96 v0 v2
-- Once.Arith.SigOp.Builders.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_152 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_152 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_138
      v0 v2
-- Once.Arith.SigOp.Builders.M.coerce-round-trip
d_coerce'45'round'45'trip_154 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_154 = erased
-- Once.Arith.SigOp.Builders.M.coerce-struct
d_coerce'45'struct_156 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct_156
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct_268
-- Once.Arith.SigOp.Builders.M.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_158 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_158 = erased
-- Once.Arith.SigOp.Builders.M.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_160 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_160
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct'8315''185'_274
-- Once.Arith.SigOp.Builders.M.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_162 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_162 = erased
-- Once.Arith.SigOp.Builders.M.coerce-μ-in
d_coerce'45'μ'45'in_164 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_164 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'in_748 v0 v2
-- Once.Arith.SigOp.Builders.M.coerce-μ-out
d_coerce'45'μ'45'out_166 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_166 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_790 v0 v1
      v3
-- Once.Arith.SigOp.Builders.M.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_168 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_168 = erased
-- Once.Arith.SigOp.Builders.M.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_170 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_170 = erased
-- Once.Arith.SigOp.Builders.M.coerce-ν-in
d_coerce'45'ν'45'in_172 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_172
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_982
-- Once.Arith.SigOp.Builders.M.coerce-ν-out
d_coerce'45'ν'45'out_174 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_174
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'out_988
-- Once.Arith.SigOp.Builders.M.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_176 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_176 = erased
-- Once.Arith.SigOp.Builders.M.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_178 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_178 = erased
-- Once.Arith.SigOp.Builders.M.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_180 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_180 = erased
-- Once.Arith.SigOp.Builders.M.fmap-struct-coherence
d_fmap'45'struct'45'coherence_182 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_182 = erased
-- Once.Arith.SigOp.Builders.M.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_184 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_184 = erased
-- Once.Arith.SigOp.Builders.M.sem-CoIn
d_sem'45'CoIn_186 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'CoIn_186
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoIn_1002
-- Once.Arith.SigOp.Builders.M.sem-CoOut
d_sem'45'CoOut_188 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 -> AgdaAny
d_sem'45'CoOut_188
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoOut_992
-- Once.Arith.SigOp.Builders.M.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_190 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_190 = erased
-- Once.Arith.SigOp.Builders.M.sem-In
d_sem'45'In_192 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_μS_182
d_sem'45'In_192
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'In_922
-- Once.Arith.SigOp.Builders.M.sem-In-Out
d_sem'45'In'45'Out_194 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_194 = erased
-- Once.Arith.SigOp.Builders.M.sem-Out
d_sem'45'Out_196 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'Out_196
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'Out_930
-- Once.Arith.SigOp.Builders.M.sem-Out-In
d_sem'45'Out'45'In_198 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_198 = erased
-- Once.Arith.SigOp.Builders.M.sem-ana
d_sem'45'ana_200 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'ana_200 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'ana_1026 v0 v2 v3
-- Once.Arith.SigOp.Builders.M.sem-case
d_sem'45'case_202 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_202 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'case_332 v3 v4 v5
-- Once.Arith.SigOp.Builders.M.sem-case-inl
d_sem'45'case'45'inl_204 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_204 = erased
-- Once.Arith.SigOp.Builders.M.sem-case-inr
d_sem'45'case'45'inr_206 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_206 = erased
-- Once.Arith.SigOp.Builders.M.sem-cata
d_sem'45'cata_208 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'cata_208 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_942 v0 v1 v3
-- Once.Arith.SigOp.Builders.M.sem-cata-compute
d_sem'45'cata'45'compute_210 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_210 = erased
-- Once.Arith.SigOp.Builders.M.sem-fmap
d_sem'45'fmap_212 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_212 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_420 v0 v3 v4
-- Once.Arith.SigOp.Builders.M.sem-fmap-Type
d_sem'45'fmap'45'Type_214 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_214 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap'45'Type_464 v0 v3
      v4
-- Once.Arith.SigOp.Builders.M.sem-fst
d_sem'45'fst_216 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_216 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fst_296 v2
-- Once.Arith.SigOp.Builders.M.sem-fst-pair
d_sem'45'fst'45'pair_218 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_218 = erased
-- Once.Arith.SigOp.Builders.M.sem-functor-coherence
d_sem'45'functor'45'coherence_220 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_220 = erased
-- Once.Arith.SigOp.Builders.M.sem-fuseNat
d_sem'45'fuseNat_222 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'fuseNat_222 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat_1156 v0 v1 v2
      v3 v5 v6
-- Once.Arith.SigOp.Builders.M.sem-fuseNat-cong
d_sem'45'fuseNat'45'cong_224 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (() ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fuseNat'45'cong_224 = erased
-- Once.Arith.SigOp.Builders.M.sem-fuseNat-events
d_sem'45'fuseNat'45'events_226 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'fuseNat'45'events_226 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat'45'events_1252
      v1 v2 v3 v4 v5 v6 v8 v9
-- Once.Arith.SigOp.Builders.M.sem-inl
d_sem'45'inl_228 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_228 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inl_318
-- Once.Arith.SigOp.Builders.M.sem-inr
d_sem'45'inr_230 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_230 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inr_324
-- Once.Arith.SigOp.Builders.M.sem-pair
d_sem'45'pair_232 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_232 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'pair_308 v2 v3
-- Once.Arith.SigOp.Builders.M.sem-para
d_sem'45'para_234 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'para_234 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'para_958 v0 v1 v3 v4
-- Once.Arith.SigOp.Builders.M.sem-snd
d_sem'45'snd_236 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_236 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'snd_302 v2
-- Once.Arith.SigOp.Builders.M.sem-snd-pair
d_sem'45'snd'45'pair_238 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_238 = erased
-- Once.Arith.SigOp.Builders.M.sfmapSemAna
d_sfmapSemAna_240 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmapSemAna_240 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sfmapSemAna_1034 v0 v1 v3 v4
-- Once.Arith.SigOp.Builders.M.sfmapSemAna-is-sfmap
d_sfmapSemAna'45'is'45'sfmap_242 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapSemAna'45'is'45'sfmap_242 = erased
-- Once.Arith.SigOp.Builders.M.⟦_⟧
d_'10214'_'10215'_244 :: MAlonzo.Code.Once.Type.T_Type_112 -> ()
d_'10214'_'10215'_244 = erased
-- Once.Arith.SigOp.Builders.M.⟦_⟧F
d_'10214'_'10215'F_246 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> ()
d_'10214'_'10215'F_246 = erased
-- Once.Arith.SigOp.Builders.M.⟦μ⟧
d_'10214'μ'10215'_248 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'μ'10215'_248 = erased
-- Once.Arith.SigOp.Builders.M.⟦ν⟧
d_'10214'ν'10215'_250 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'ν'10215'_250 = erased
-- Once.Arith.SigOp.Builders.add-semM
d_add'45'semM_252 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_add'45'semM_252 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe
             MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer)) (coe v1)
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.sub-semM
d_sub'45'semM_258 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_sub'45'semM_258 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe
             MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer)) (coe v1)
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.mul-semM
d_mul'45'semM_264 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_mul'45'semM_264 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe
             MAlonzo.Code.Once.Word.d__'8855'__38 (coe (64 :: Integer)) (coe v1)
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.neg-semM
d_neg'45'semM_270 :: Integer -> Integer
d_neg'45'semM_270 v0
  = coe
      MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer)) (coe v0)
-- Once.Arith.SigOp.Builders.div-semM
d_div'45'semM_274
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.div-semM"
-- Once.Arith.SigOp.Builders.mod-semM
d_mod'45'semM_276
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.mod-semM"
-- Once.Arith.SigOp.Builders.lt-semM
d_lt'45'semM_278
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.lt-semM"
-- Once.Arith.SigOp.Builders.le-semM
d_le'45'semM_280
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.le-semM"
-- Once.Arith.SigOp.Builders.gt-semM
d_gt'45'semM_282
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.gt-semM"
-- Once.Arith.SigOp.Builders.ge-semM
d_ge'45'semM_284
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.ge-semM"
-- Once.Arith.SigOp.Builders.eq-semM
d_eq'45'semM_286
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.eq-semM"
-- Once.Arith.SigOp.Builders.ne-semM
d_ne'45'semM_288
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.ne-semM"
-- Once.Arith.SigOp.Builders.str-lit-semM
d_str'45'lit'45'semM_290 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_str'45'lit'45'semM_290 v0 ~v1 = du_str'45'lit'45'semM_290 v0
du_str'45'lit'45'semM_290 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_str'45'lit'45'semM_290 v0 = coe v0
-- Once.Arith.SigOp.Builders.base-I×I
d_base'45'I'215'I_294 ::
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200
d_base'45'I'215'I_294
  = coe
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_218
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206)
-- Once.Arith.SigOp.Builders.con-Int
d_con'45'Int_296 ::
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226
d_con'45'Int_296
  = coe
      MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206)
-- Once.Arith.SigOp.Builders.con-U+U
d_con'45'U'43'U_298 ::
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226
d_con'45'U'43'U_298
  = coe
      MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230
      (coe
         MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_224
         (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)
         (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202))
-- Once.Arith.SigOp.Builders.add-info
d_add'45'info_300 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_add'45'info_300
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.add.int" :: Data.Text.Text)))
      (coe d_add'45'semM_252)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_294) (coe d_con'45'Int_296)
-- Once.Arith.SigOp.Builders.sub-info
d_sub'45'info_302 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_sub'45'info_302
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.sub.int" :: Data.Text.Text)))
      (coe d_sub'45'semM_258)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_294) (coe d_con'45'Int_296)
-- Once.Arith.SigOp.Builders.mul-info
d_mul'45'info_304 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_mul'45'info_304
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.mul.int" :: Data.Text.Text)))
      (coe d_mul'45'semM_264)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_294) (coe d_con'45'Int_296)
-- Once.Arith.SigOp.Builders.div-info
d_div'45'info_306 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_div'45'info_306
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.div.int" :: Data.Text.Text)))
      (coe d_div'45'semM_274)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_294) (coe d_con'45'Int_296)
-- Once.Arith.SigOp.Builders.mod-info
d_mod'45'info_308 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_mod'45'info_308
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.mod.int" :: Data.Text.Text)))
      (coe d_mod'45'semM_276)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_294) (coe d_con'45'Int_296)
-- Once.Arith.SigOp.Builders.neg-info
d_neg'45'info_310 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_neg'45'info_310
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.neg.int" :: Data.Text.Text)))
      (coe d_neg'45'semM_270)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206)
      (coe d_con'45'Int_296)
-- Once.Arith.SigOp.Builders.lt-info
d_lt'45'info_312 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_lt'45'info_312
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.lt.int" :: Data.Text.Text)))
      (coe d_lt'45'semM_278)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_294) (coe d_con'45'U'43'U_298)
-- Once.Arith.SigOp.Builders.le-info
d_le'45'info_314 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_le'45'info_314
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.le.int" :: Data.Text.Text)))
      (coe d_le'45'semM_280)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_294) (coe d_con'45'U'43'U_298)
-- Once.Arith.SigOp.Builders.gt-info
d_gt'45'info_316 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_gt'45'info_316
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.gt.int" :: Data.Text.Text)))
      (coe d_gt'45'semM_282)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_294) (coe d_con'45'U'43'U_298)
-- Once.Arith.SigOp.Builders.ge-info
d_ge'45'info_318 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_ge'45'info_318
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.ge.int" :: Data.Text.Text)))
      (coe d_ge'45'semM_284)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_294) (coe d_con'45'U'43'U_298)
-- Once.Arith.SigOp.Builders.eq-info
d_eq'45'info_320 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_eq'45'info_320
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.eq.int" :: Data.Text.Text)))
      (coe d_eq'45'semM_286)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_294) (coe d_con'45'U'43'U_298)
-- Once.Arith.SigOp.Builders.ne-info
d_ne'45'info_322 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_ne'45'info_322
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.ne.int" :: Data.Text.Text)))
      (coe d_ne'45'semM_288)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_294) (coe d_con'45'U'43'U_298)
-- Once.Arith.SigOp.Builders.str-lit-info
d_str'45'lit'45'info_324 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_str'45'lit'45'info_324 v0
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            ("lit.str." :: Data.Text.Text) v0))
      (coe (\ v1 -> v0)) (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)
      (coe
         MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230
         (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Str_210))
-- Once.Arith.SigOp.Builders.generic-semM
d_generic'45'semM_332
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.generic-semM"
-- Once.Arith.SigOp.Builders.value-info
d_value'45'info_338 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_value'45'info_338 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234 (coe v2)
      (coe
         d_generic'45'semM_332 v0 v1
         (MAlonzo.Code.Once.CanonicalName.d_showCanonical_40 (coe v2)))
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124) (coe v3) (coe v4)
-- Once.Arith.SigOp.Builders.internal-info
d_internal'45'info_348 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_internal'45'info_348 v0 v1
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_182 (coe v1)
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_pureV_140
         (coe
            d_generic'45'semM_332 (coe MAlonzo.Code.Once.Type.C_Unit_122) v0
            (MAlonzo.Code.Once.CanonicalName.d_showCanonical_40 (coe v1))))
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)
      (coe MAlonzo.Code.Once.SigOp.Info.C_internal'45'ref_154)
-- Once.Arith.SigOp.Builders.generic-info
d_generic'45'info_356 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_generic'45'info_356 v0 v1
  = coe d_value'45'info_338 (coe v0) (coe v1)
-- Once.Arith.SigOp.Builders.arrow-info-eff
d_arrow'45'info'45'eff_362 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_arrow'45'info'45'eff_362 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
        -> if coe v6
             then coe
                    seq (coe v7)
                    (coe
                       MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_182 (coe v2)
                       (coe MAlonzo.Code.Once.SigOp.Info.C_emitsV_142) (coe v4)
                       (coe MAlonzo.Code.Once.SigOp.Info.C_ffi'45'concrete_152 (coe v5)))
             else coe
                    seq (coe v7)
                    (coe
                       d_value'45'info_338 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.arrow-info
d_arrow'45'info_380 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_arrow'45'info_380 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      MAlonzo.Code.Once.Type.C_mk'45'kind_50 v6 v7
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C_pure_34
               -> coe
                    d_value'45'info_338 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
             MAlonzo.Code.Once.Type.C_eff_36
               -> coe
                    d_arrow'45'info'45'eff_362 (coe v0) (coe v1) (coe v3)
                    (coe MAlonzo.Code.Once.Type.d_isUnit'63'_164 (coe v1)) (coe v4)
                    (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
