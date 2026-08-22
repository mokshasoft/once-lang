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
      MAlonzo.Code.Once.Word.d__'37''738'__126 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W._/ˢ_
d__'47''738'__12 :: Integer -> Integer -> Integer
d__'47''738'__12
  = coe
      MAlonzo.Code.Once.Word.d__'47''738'__120 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W._<ˢ_
d__'60''738'__14 :: Integer -> Integer -> Bool
d__'60''738'__14
  = coe MAlonzo.Code.Once.Word.d__'60''738'__80 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W._≡ʷ_
d__'8801''695'__16 :: Integer -> Integer -> Bool
d__'8801''695'__16 = coe MAlonzo.Code.Once.Word.du__'8801''695'__86
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
      MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_548
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
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_514
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
d_0'60'half_46 = coe MAlonzo.Code.Once.Word.du_0'60'half_168
-- Once.Arith.SigOp.Builders.W.0<modulus
d_0'60'modulus_48 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_48 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_166
-- Once.Arith.SigOp.Builders.W.0<negOne
d_0'60'negOne_50 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_50 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_370 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.1<modulus
d_1'60'modulus_52 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_52
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_650 (coe (64 :: Integer))
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
      MAlonzo.Code.Once.Word.du_2'8804'modulus_366 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.InRange
d_InRange_58 :: Integer -> ()
d_InRange_58 = erased
-- Once.Arith.SigOp.Builders.W.Word
d_Word_60 :: ()
d_Word_60 = erased
-- Once.Arith.SigOp.Builders.W.fromℤ
d_fromℤ_62 :: Integer -> Integer
d_fromℤ_62
  = coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.fromℤ-0
d_fromℤ'45'0_64 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_64 = erased
-- Once.Arith.SigOp.Builders.W.fromℤ-in-range
d_fromℤ'45'in'45'range_66 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_66
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_174
      (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_68 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_68 = erased
-- Once.Arith.SigOp.Builders.W.fromℤ-neg1
d_fromℤ'45'neg1_70 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_70 = erased
-- Once.Arith.SigOp.Builders.W.half
d_half_72 :: Integer
d_half_72
  = coe MAlonzo.Code.Once.Word.d_half_48 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.half<modulus
d_half'60'modulus_74 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_74 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_374 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.half≡2^b
d_half'8801'2'94'b_76 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_76 = erased
-- Once.Arith.SigOp.Builders.W.half≤negOne
d_half'8804'negOne_78 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_78 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_394
      (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.inRange?
d_inRange'63'_80 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_80
  = coe MAlonzo.Code.Once.Word.d_inRange'63'_62 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.intMin
d_intMin_82 :: Integer
d_intMin_82
  = coe MAlonzo.Code.Once.Word.d_intMin_54 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.modulus
d_modulus_84 :: Integer
d_modulus_84
  = coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_86 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_86 = erased
-- Once.Arith.SigOp.Builders.W.modulus≢0
d_modulus'8802'0_88 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_88
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.mod∸half≡half
d_mod'8760'half'8801'half_90 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_90 = erased
-- Once.Arith.SigOp.Builders.W.mod≡half+half
d_mod'8801'half'43'half_92 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_92 = erased
-- Once.Arith.SigOp.Builders.W.negOne
d_negOne_94 :: Integer
d_negOne_94
  = coe MAlonzo.Code.Once.Word.d_negOne_78 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.negOne<modulus
d_negOne'60'modulus_96 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_96 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_382
      (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.negOne≢0
d_negOne'8802'0_98 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_98 = erased
-- Once.Arith.SigOp.Builders.W.norm
d_norm_100 :: Integer -> Integer
d_norm_100
  = coe MAlonzo.Code.Once.Word.d_norm_16 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.norm-0
d_norm'45'0_102 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_102 = erased
-- Once.Arith.SigOp.Builders.W.norm-id
d_norm'45'id_104 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_104 = erased
-- Once.Arith.SigOp.Builders.W.sdiv2ᵏ
d_sdiv2'7503'_106 :: Integer -> Integer -> Integer
d_sdiv2'7503'_106
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_138 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.shlᵂ
d_shl'7490'_108 :: Integer -> Integer -> Integer
d_shl'7490'_108
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_132 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.sucNegOne≡mod
d_sucNegOne'8801'mod_110 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_110 = erased
-- Once.Arith.SigOp.Builders.W.tdiv-neg1
d_tdiv'45'neg1_112 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_112 = erased
-- Once.Arith.SigOp.Builders.W.tmod-neg1
d_tmod'45'neg1_114 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_114 = erased
-- Once.Arith.SigOp.Builders.W.toWord
d_toWord_116 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_116 v0 v1
  = coe MAlonzo.Code.Once.Word.du_toWord_68 (coe (64 :: Integer)) v0
-- Once.Arith.SigOp.Builders.W.toWord≡fromℤ
d_toWord'8801'fromℤ_118 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'8801'fromℤ_118 = erased
-- Once.Arith.SigOp.Builders.W.toℤ
d_toℤ_120 :: Integer -> Integer
d_toℤ_120
  = coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.toℤ-negOne
d_toℤ'45'negOne_122 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_122 = erased
-- Once.Arith.SigOp.Builders.W.≡ᵇ-refl
d_'8801''7495''45'refl_124 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_124 = erased
-- Once.Arith.SigOp.Builders.W.≡ᵇ0-false
d_'8801''7495'0'45'false_126 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_126 = erased
-- Once.Arith.SigOp.Builders.W.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_128 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_128 = erased
-- Once.Arith.SigOp.Builders.W.⊕-neg
d_'8853''45'neg_130 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_130 = erased
-- Once.Arith.SigOp.Builders.W.⊕-neg-suc
d_'8853''45'neg'45'suc_132 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_132 = erased
-- Once.Arith.SigOp.Builders.W.⊕-normʳ
d_'8853''45'norm'691'_134 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_134 = erased
-- Once.Arith.SigOp.Builders.W.⊕≡+
d_'8853''8801''43'_136 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_136 = erased
-- Once.Arith.SigOp.Builders.W.⊖-normʳ
d_'8854''45'norm'691'_138 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_138 = erased
-- Once.Arith.SigOp.Builders.W.⊖≡∸
d_'8854''8801''8760'_140 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_140 = erased
-- Once.Arith.SigOp.Builders.W.⊗-pow2
d_'8855''45'pow2_142 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_142 = erased
-- Once.Arith.SigOp.Builders.W.⊝_
d_'8861'__144 :: Integer -> Integer
d_'8861'__144
  = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
-- Once.Arith.SigOp.Builders.W.⊝-intMin
d_'8861''45'intMin_146 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_146 = erased
-- Once.Arith.SigOp.Builders.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_150 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_150
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'base'45'to'45'full_636
-- Once.Arith.SigOp.Builders.M.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_152 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_152 = erased
-- Once.Arith.SigOp.Builders.M.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_154 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_154 = erased
-- Once.Arith.SigOp.Builders.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_156 ::
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_156
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'full'45'to'45'base_600
-- Once.Arith.SigOp.Builders.M.coerce-functor
d_coerce'45'functor_158 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor_158 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_96 v0 v2
-- Once.Arith.SigOp.Builders.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_160 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_160 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_138
      v0 v2
-- Once.Arith.SigOp.Builders.M.coerce-round-trip
d_coerce'45'round'45'trip_162 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_162 = erased
-- Once.Arith.SigOp.Builders.M.coerce-struct
d_coerce'45'struct_164 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct_164
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct_268
-- Once.Arith.SigOp.Builders.M.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_166 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_166 = erased
-- Once.Arith.SigOp.Builders.M.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_168 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_168
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct'8315''185'_274
-- Once.Arith.SigOp.Builders.M.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_170 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_170 = erased
-- Once.Arith.SigOp.Builders.M.coerce-μ-in
d_coerce'45'μ'45'in_172 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_172 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'in_748 v0 v2
-- Once.Arith.SigOp.Builders.M.coerce-μ-out
d_coerce'45'μ'45'out_174 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_174 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_790 v0 v1
      v3
-- Once.Arith.SigOp.Builders.M.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_176 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_176 = erased
-- Once.Arith.SigOp.Builders.M.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_178 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_178 = erased
-- Once.Arith.SigOp.Builders.M.coerce-ν-in
d_coerce'45'ν'45'in_180 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_180
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_982
-- Once.Arith.SigOp.Builders.M.coerce-ν-out
d_coerce'45'ν'45'out_182 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_182
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'out_988
-- Once.Arith.SigOp.Builders.M.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_184 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_184 = erased
-- Once.Arith.SigOp.Builders.M.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_186 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_186 = erased
-- Once.Arith.SigOp.Builders.M.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_188 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_188 = erased
-- Once.Arith.SigOp.Builders.M.fmap-struct-coherence
d_fmap'45'struct'45'coherence_190 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_190 = erased
-- Once.Arith.SigOp.Builders.M.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_192 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_192 = erased
-- Once.Arith.SigOp.Builders.M.sem-CoIn
d_sem'45'CoIn_194 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'CoIn_194
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoIn_1002
-- Once.Arith.SigOp.Builders.M.sem-CoOut
d_sem'45'CoOut_196 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 -> AgdaAny
d_sem'45'CoOut_196
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoOut_992
-- Once.Arith.SigOp.Builders.M.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_198 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_198 = erased
-- Once.Arith.SigOp.Builders.M.sem-In
d_sem'45'In_200 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_μS_182
d_sem'45'In_200
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'In_922
-- Once.Arith.SigOp.Builders.M.sem-In-Out
d_sem'45'In'45'Out_202 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_202 = erased
-- Once.Arith.SigOp.Builders.M.sem-Out
d_sem'45'Out_204 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'Out_204
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'Out_930
-- Once.Arith.SigOp.Builders.M.sem-Out-In
d_sem'45'Out'45'In_206 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_206 = erased
-- Once.Arith.SigOp.Builders.M.sem-ana
d_sem'45'ana_208 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'ana_208 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'ana_1026 v0 v2 v3
-- Once.Arith.SigOp.Builders.M.sem-case
d_sem'45'case_210 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_210 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'case_332 v3 v4 v5
-- Once.Arith.SigOp.Builders.M.sem-case-inl
d_sem'45'case'45'inl_212 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_212 = erased
-- Once.Arith.SigOp.Builders.M.sem-case-inr
d_sem'45'case'45'inr_214 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_214 = erased
-- Once.Arith.SigOp.Builders.M.sem-cata
d_sem'45'cata_216 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'cata_216 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_942 v0 v1 v3
-- Once.Arith.SigOp.Builders.M.sem-cata-compute
d_sem'45'cata'45'compute_218 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_218 = erased
-- Once.Arith.SigOp.Builders.M.sem-fmap
d_sem'45'fmap_220 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_220 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_420 v0 v3 v4
-- Once.Arith.SigOp.Builders.M.sem-fmap-Type
d_sem'45'fmap'45'Type_222 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_222 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap'45'Type_464 v0 v3
      v4
-- Once.Arith.SigOp.Builders.M.sem-fst
d_sem'45'fst_224 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_224 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fst_296 v2
-- Once.Arith.SigOp.Builders.M.sem-fst-pair
d_sem'45'fst'45'pair_226 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_226 = erased
-- Once.Arith.SigOp.Builders.M.sem-functor-coherence
d_sem'45'functor'45'coherence_228 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_228 = erased
-- Once.Arith.SigOp.Builders.M.sem-fuseNat
d_sem'45'fuseNat_230 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'fuseNat_230 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat_1156 v0 v1 v2
      v3 v5 v6
-- Once.Arith.SigOp.Builders.M.sem-fuseNat-cong
d_sem'45'fuseNat'45'cong_232 ::
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
d_sem'45'fuseNat'45'cong_232 = erased
-- Once.Arith.SigOp.Builders.M.sem-fuseNat-events
d_sem'45'fuseNat'45'events_234 ::
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
d_sem'45'fuseNat'45'events_234 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat'45'events_1252
      v1 v2 v3 v4 v5 v6 v8 v9
-- Once.Arith.SigOp.Builders.M.sem-inl
d_sem'45'inl_236 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_236 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inl_318
-- Once.Arith.SigOp.Builders.M.sem-inr
d_sem'45'inr_238 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_238 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inr_324
-- Once.Arith.SigOp.Builders.M.sem-pair
d_sem'45'pair_240 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_240 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'pair_308 v2 v3
-- Once.Arith.SigOp.Builders.M.sem-para
d_sem'45'para_242 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'para_242 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'para_958 v0 v1 v3 v4
-- Once.Arith.SigOp.Builders.M.sem-snd
d_sem'45'snd_244 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_244 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'snd_302 v2
-- Once.Arith.SigOp.Builders.M.sem-snd-pair
d_sem'45'snd'45'pair_246 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_246 = erased
-- Once.Arith.SigOp.Builders.M.sfmapSemAna
d_sfmapSemAna_248 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmapSemAna_248 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sfmapSemAna_1034 v0 v1 v3 v4
-- Once.Arith.SigOp.Builders.M.sfmapSemAna-is-sfmap
d_sfmapSemAna'45'is'45'sfmap_250 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapSemAna'45'is'45'sfmap_250 = erased
-- Once.Arith.SigOp.Builders.M.⟦_⟧
d_'10214'_'10215'_252 :: MAlonzo.Code.Once.Type.T_Type_112 -> ()
d_'10214'_'10215'_252 = erased
-- Once.Arith.SigOp.Builders.M.⟦_⟧F
d_'10214'_'10215'F_254 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> ()
d_'10214'_'10215'F_254 = erased
-- Once.Arith.SigOp.Builders.M.⟦μ⟧
d_'10214'μ'10215'_256 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'μ'10215'_256 = erased
-- Once.Arith.SigOp.Builders.M.⟦ν⟧
d_'10214'ν'10215'_258 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'ν'10215'_258 = erased
-- Once.Arith.SigOp.Builders.add-semM
d_add'45'semM_260 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_add'45'semM_260 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe
             MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer)) (coe v1)
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.sub-semM
d_sub'45'semM_266 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_sub'45'semM_266 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe
             MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer)) (coe v1)
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.mul-semM
d_mul'45'semM_272 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_mul'45'semM_272 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe
             MAlonzo.Code.Once.Word.d__'8855'__38 (coe (64 :: Integer)) (coe v1)
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.neg-semM
d_neg'45'semM_278 :: Integer -> Integer
d_neg'45'semM_278 v0
  = coe
      MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer)) (coe v0)
-- Once.Arith.SigOp.Builders.div-semM
d_div'45'semM_282
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.div-semM"
-- Once.Arith.SigOp.Builders.mod-semM
d_mod'45'semM_284
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.mod-semM"
-- Once.Arith.SigOp.Builders.lt-semM
d_lt'45'semM_286
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.lt-semM"
-- Once.Arith.SigOp.Builders.le-semM
d_le'45'semM_288
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.le-semM"
-- Once.Arith.SigOp.Builders.gt-semM
d_gt'45'semM_290
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.gt-semM"
-- Once.Arith.SigOp.Builders.ge-semM
d_ge'45'semM_292
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.ge-semM"
-- Once.Arith.SigOp.Builders.eq-semM
d_eq'45'semM_294
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.eq-semM"
-- Once.Arith.SigOp.Builders.ne-semM
d_ne'45'semM_296
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.ne-semM"
-- Once.Arith.SigOp.Builders.str-lit-semM
d_str'45'lit'45'semM_298 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_str'45'lit'45'semM_298 v0 ~v1 = du_str'45'lit'45'semM_298 v0
du_str'45'lit'45'semM_298 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_str'45'lit'45'semM_298 v0 = coe v0
-- Once.Arith.SigOp.Builders.base-I×I
d_base'45'I'215'I_302 ::
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200
d_base'45'I'215'I_302
  = coe
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_218
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206)
-- Once.Arith.SigOp.Builders.con-Int
d_con'45'Int_304 ::
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226
d_con'45'Int_304
  = coe
      MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206)
-- Once.Arith.SigOp.Builders.con-U+U
d_con'45'U'43'U_306 ::
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226
d_con'45'U'43'U_306
  = coe
      MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230
      (coe
         MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_224
         (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)
         (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202))
-- Once.Arith.SigOp.Builders.add-info
d_add'45'info_308 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_add'45'info_308
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.add.int" :: Data.Text.Text)))
      (coe d_add'45'semM_260)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_302) (coe d_con'45'Int_304)
-- Once.Arith.SigOp.Builders.sub-info
d_sub'45'info_310 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_sub'45'info_310
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.sub.int" :: Data.Text.Text)))
      (coe d_sub'45'semM_266)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_302) (coe d_con'45'Int_304)
-- Once.Arith.SigOp.Builders.mul-info
d_mul'45'info_312 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_mul'45'info_312
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.mul.int" :: Data.Text.Text)))
      (coe d_mul'45'semM_272)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_302) (coe d_con'45'Int_304)
-- Once.Arith.SigOp.Builders.div-info
d_div'45'info_314 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_div'45'info_314
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.div.int" :: Data.Text.Text)))
      (coe d_div'45'semM_282)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_302) (coe d_con'45'Int_304)
-- Once.Arith.SigOp.Builders.mod-info
d_mod'45'info_316 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_mod'45'info_316
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.mod.int" :: Data.Text.Text)))
      (coe d_mod'45'semM_284)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_302) (coe d_con'45'Int_304)
-- Once.Arith.SigOp.Builders.neg-info
d_neg'45'info_318 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_neg'45'info_318
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.neg.int" :: Data.Text.Text)))
      (coe d_neg'45'semM_278)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206)
      (coe d_con'45'Int_304)
-- Once.Arith.SigOp.Builders.lt-info
d_lt'45'info_320 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_lt'45'info_320
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.lt.int" :: Data.Text.Text)))
      (coe d_lt'45'semM_286)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_302) (coe d_con'45'U'43'U_306)
-- Once.Arith.SigOp.Builders.le-info
d_le'45'info_322 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_le'45'info_322
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.le.int" :: Data.Text.Text)))
      (coe d_le'45'semM_288)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_302) (coe d_con'45'U'43'U_306)
-- Once.Arith.SigOp.Builders.gt-info
d_gt'45'info_324 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_gt'45'info_324
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.gt.int" :: Data.Text.Text)))
      (coe d_gt'45'semM_290)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_302) (coe d_con'45'U'43'U_306)
-- Once.Arith.SigOp.Builders.ge-info
d_ge'45'info_326 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_ge'45'info_326
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.ge.int" :: Data.Text.Text)))
      (coe d_ge'45'semM_292)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_302) (coe d_con'45'U'43'U_306)
-- Once.Arith.SigOp.Builders.eq-info
d_eq'45'info_328 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_eq'45'info_328
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.eq.int" :: Data.Text.Text)))
      (coe d_eq'45'semM_294)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_302) (coe d_con'45'U'43'U_306)
-- Once.Arith.SigOp.Builders.ne-info
d_ne'45'info_330 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_ne'45'info_330
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.ne.int" :: Data.Text.Text)))
      (coe d_ne'45'semM_296)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_302) (coe d_con'45'U'43'U_306)
-- Once.Arith.SigOp.Builders.str-lit-info
d_str'45'lit'45'info_332 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_str'45'lit'45'info_332 v0
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
d_generic'45'semM_340
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.generic-semM"
-- Once.Arith.SigOp.Builders.value-info
d_value'45'info_346 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_value'45'info_346 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234 (coe v2)
      (coe
         d_generic'45'semM_340 v0 v1
         (MAlonzo.Code.Once.CanonicalName.d_showCanonical_40 (coe v2)))
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124) (coe v3) (coe v4)
-- Once.Arith.SigOp.Builders.internal-info
d_internal'45'info_356 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_internal'45'info_356 v0 v1
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_182 (coe v1)
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_pureV_140
         (coe
            d_generic'45'semM_340 (coe MAlonzo.Code.Once.Type.C_Unit_122) v0
            (MAlonzo.Code.Once.CanonicalName.d_showCanonical_40 (coe v1))))
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)
      (coe MAlonzo.Code.Once.SigOp.Info.C_internal'45'ref_154)
-- Once.Arith.SigOp.Builders.generic-info
d_generic'45'info_364 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_generic'45'info_364 v0 v1
  = coe d_value'45'info_346 (coe v0) (coe v1)
-- Once.Arith.SigOp.Builders.arrow-info-eff
d_arrow'45'info'45'eff_370 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_arrow'45'info'45'eff_370 v0 v1 v2 v3 v4 v5
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
                       d_value'45'info_346 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.arrow-info
d_arrow'45'info_388 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_arrow'45'info_388 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      MAlonzo.Code.Once.Type.C_mk'45'kind_50 v6 v7
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C_pure_34
               -> coe
                    d_value'45'info_346 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
             MAlonzo.Code.Once.Type.C_eff_36
               -> coe
                    d_arrow'45'info'45'eff_370 (coe v0) (coe v1) (coe v3)
                    (coe MAlonzo.Code.Once.Type.d_isUnit'63'_164 (coe v1)) (coe v4)
                    (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
