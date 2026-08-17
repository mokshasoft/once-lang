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

module MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax
import qualified MAlonzo.Code.Once.Target.RiscV64.PhysReg
import qualified MAlonzo.Code.Once.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Target.RiscV64.Semantics.W._%ˢ_
d__'37''738'__12 :: Integer -> Integer -> Integer
d__'37''738'__12
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__104 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W._/ˢ_
d__'47''738'__14 :: Integer -> Integer -> Integer
d__'47''738'__14
  = coe MAlonzo.Code.Once.Word.d__'47''738'__98 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W._<ˢ_
d__'60''738'__16 :: Integer -> Integer -> Bool
d__'60''738'__16
  = coe MAlonzo.Code.Once.Word.d__'60''738'__58 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W._≡ʷ_
d__'8801''695'__18 :: Integer -> Integer -> Bool
d__'8801''695'__18 = coe MAlonzo.Code.Once.Word.du__'8801''695'__64
-- Once.CCC.Target.RiscV64.Semantics.W._⊕_
d__'8853'__20 :: Integer -> Integer -> Integer
d__'8853'__20
  = coe MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W._⊖_
d__'8854'__22 :: Integer -> Integer -> Integer
d__'8854'__22
  = coe MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W._⊗_
d__'8855'__24 :: Integer -> Integer -> Integer
d__'8855'__24
  = coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.%ˢ-else
d_'37''738''45'else_26 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_26 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.%ˢ-in-range
d_'37''738''45'in'45'range_28 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_28 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_526
      (coe (64 :: Integer)) v2 v3 v4
-- Once.CCC.Target.RiscV64.Semantics.W.%ˢ-mid
d_'37''738''45'mid_30 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_30 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.%ˢ-negOne
d_'37''738''45'negOne_32 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_32 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.%ˢ-zero
d_'37''738''45'zero_34 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_34 = erased
-- Once.CCC.Target.RiscV64.Semantics.W./ˢ-else
d_'47''738''45'else_36 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_36 = erased
-- Once.CCC.Target.RiscV64.Semantics.W./ˢ-in-range
d_'47''738''45'in'45'range_38 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_38 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_492
      (coe (64 :: Integer)) v2 v3
-- Once.CCC.Target.RiscV64.Semantics.W./ˢ-mid
d_'47''738''45'mid_40 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_40 = erased
-- Once.CCC.Target.RiscV64.Semantics.W./ˢ-negOne
d_'47''738''45'negOne_42 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_42 = erased
-- Once.CCC.Target.RiscV64.Semantics.W./ˢ-pow2
d_'47''738''45'pow2_44 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_44 = erased
-- Once.CCC.Target.RiscV64.Semantics.W./ˢ-zero
d_'47''738''45'zero_46 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_46 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.0<half
d_0'60'half_48 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_48 = coe MAlonzo.Code.Once.Word.du_0'60'half_146
-- Once.CCC.Target.RiscV64.Semantics.W.0<modulus
d_0'60'modulus_50 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_50 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_144
-- Once.CCC.Target.RiscV64.Semantics.W.0<negOne
d_0'60'negOne_52 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_52 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_348 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.1<modulus
d_1'60'modulus_54 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_54
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_628 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.2*n≡n+n
d_2'42'n'8801'n'43'n_56 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_56 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.2≤modulus
d_2'8804'modulus_58 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_58 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_344 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.Word
d_Word_60 :: ()
d_Word_60 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.fromℤ
d_fromℤ_62 :: Integer -> Integer
d_fromℤ_62
  = coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.fromℤ-0
d_fromℤ'45'0_64 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_64 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.fromℤ-in-range
d_fromℤ'45'in'45'range_66 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_66
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_152
      (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_68 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_68 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.fromℤ-neg1
d_fromℤ'45'neg1_70 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_70 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.half
d_half_72 :: Integer
d_half_72
  = coe MAlonzo.Code.Once.Word.d_half_48 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.half<modulus
d_half'60'modulus_74 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_74 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_352 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.half≡2^b
d_half'8801'2'94'b_76 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_76 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.half≤negOne
d_half'8804'negOne_78 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_78 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_372
      (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.intMin
d_intMin_80 :: Integer
d_intMin_80
  = coe MAlonzo.Code.Once.Word.d_intMin_54 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.modulus
d_modulus_82 :: Integer
d_modulus_82
  = coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_84 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_84 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.modulus≢0
d_modulus'8802'0_86 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_86
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.mod∸half≡half
d_mod'8760'half'8801'half_88 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_88 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.mod≡half+half
d_mod'8801'half'43'half_90 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_90 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.negOne
d_negOne_92 :: Integer
d_negOne_92
  = coe MAlonzo.Code.Once.Word.d_negOne_56 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.negOne<modulus
d_negOne'60'modulus_94 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_94 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_360
      (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.negOne≢0
d_negOne'8802'0_96 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_96 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.norm
d_norm_98 :: Integer -> Integer
d_norm_98
  = coe MAlonzo.Code.Once.Word.d_norm_16 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.norm-0
d_norm'45'0_100 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_100 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.norm-id
d_norm'45'id_102 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_102 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.sdiv2ᵏ
d_sdiv2'7503'_104 :: Integer -> Integer -> Integer
d_sdiv2'7503'_104
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_116 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.shlᵂ
d_shl'7490'_106 :: Integer -> Integer -> Integer
d_shl'7490'_106
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_110 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.sucNegOne≡mod
d_sucNegOne'8801'mod_108 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_108 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.tdiv-neg1
d_tdiv'45'neg1_110 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_110 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.tmod-neg1
d_tmod'45'neg1_112 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_112 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.toℤ
d_toℤ_114 :: Integer -> Integer
d_toℤ_114
  = coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.toℤ-negOne
d_toℤ'45'negOne_116 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_116 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.≡ᵇ-refl
d_'8801''7495''45'refl_118 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_118 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.≡ᵇ0-false
d_'8801''7495'0'45'false_120 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_120 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_122 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_122 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.⊕-neg
d_'8853''45'neg_124 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_124 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.⊕-neg-suc
d_'8853''45'neg'45'suc_126 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_126 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.⊕-normʳ
d_'8853''45'norm'691'_128 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_128 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.⊕≡+
d_'8853''8801''43'_130 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_130 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.⊖-normʳ
d_'8854''45'norm'691'_132 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_132 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.⊖≡∸
d_'8854''8801''8760'_134 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_134 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.⊗-pow2
d_'8855''45'pow2_136 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_136 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.⊝_
d_'8861'__138 :: Integer -> Integer
d_'8861'__138
  = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.⊝-intMin
d_'8861''45'intMin_140 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_140 = erased
-- Once.CCC.Target.RiscV64.Semantics.Word
d_Word_142 :: ()
d_Word_142 = erased
-- Once.CCC.Target.RiscV64.Semantics.offsetToℕ
d_offsetToℕ_144 :: Integer -> Integer
d_offsetToℕ_144 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) -> coe v0
      _ -> coe (0 :: Integer)
-- Once.CCC.Target.RiscV64.Semantics.isNegative
d_isNegative_150 :: Integer -> Bool
d_isNegative_150 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
-- Once.CCC.Target.RiscV64.Semantics.RegFile
d_RegFile_152 = ()
data T_RegFile_152
  = C_mkregfile_234 Integer Integer Integer Integer Integer Integer
                    Integer Integer Integer Integer Integer Integer Integer Integer
                    Integer Integer Integer Integer Integer Integer
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-ra
d_get'45'ra_194 :: T_RegFile_152 -> Integer
d_get'45'ra_194 v0
  = case coe v0 of
      C_mkregfile_234 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-sp
d_get'45'sp_196 :: T_RegFile_152 -> Integer
d_get'45'sp_196 v0
  = case coe v0 of
      C_mkregfile_234 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-fp
d_get'45'fp_198 :: T_RegFile_152 -> Integer
d_get'45'fp_198 v0
  = case coe v0 of
      C_mkregfile_234 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a0
d_get'45'a0_200 :: T_RegFile_152 -> Integer
d_get'45'a0_200 v0
  = case coe v0 of
      C_mkregfile_234 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a1
d_get'45'a1_202 :: T_RegFile_152 -> Integer
d_get'45'a1_202 v0
  = case coe v0 of
      C_mkregfile_234 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a2
d_get'45'a2_204 :: T_RegFile_152 -> Integer
d_get'45'a2_204 v0
  = case coe v0 of
      C_mkregfile_234 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a3
d_get'45'a3_206 :: T_RegFile_152 -> Integer
d_get'45'a3_206 v0
  = case coe v0 of
      C_mkregfile_234 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a4
d_get'45'a4_208 :: T_RegFile_152 -> Integer
d_get'45'a4_208 v0
  = case coe v0 of
      C_mkregfile_234 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a5
d_get'45'a5_210 :: T_RegFile_152 -> Integer
d_get'45'a5_210 v0
  = case coe v0 of
      C_mkregfile_234 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a6
d_get'45'a6_212 :: T_RegFile_152 -> Integer
d_get'45'a6_212 v0
  = case coe v0 of
      C_mkregfile_234 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a7
d_get'45'a7_214 :: T_RegFile_152 -> Integer
d_get'45'a7_214 v0
  = case coe v0 of
      C_mkregfile_234 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-s1
d_get'45's1_216 :: T_RegFile_152 -> Integer
d_get'45's1_216 v0
  = case coe v0 of
      C_mkregfile_234 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-s2
d_get'45's2_218 :: T_RegFile_152 -> Integer
d_get'45's2_218 v0
  = case coe v0 of
      C_mkregfile_234 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-s3
d_get'45's3_220 :: T_RegFile_152 -> Integer
d_get'45's3_220 v0
  = case coe v0 of
      C_mkregfile_234 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-s4
d_get'45's4_222 :: T_RegFile_152 -> Integer
d_get'45's4_222 v0
  = case coe v0 of
      C_mkregfile_234 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-t0
d_get'45't0_224 :: T_RegFile_152 -> Integer
d_get'45't0_224 v0
  = case coe v0 of
      C_mkregfile_234 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-t1
d_get'45't1_226 :: T_RegFile_152 -> Integer
d_get'45't1_226 v0
  = case coe v0 of
      C_mkregfile_234 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v17
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-t2
d_get'45't2_228 :: T_RegFile_152 -> Integer
d_get'45't2_228 v0
  = case coe v0 of
      C_mkregfile_234 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-t3
d_get'45't3_230 :: T_RegFile_152 -> Integer
d_get'45't3_230 v0
  = case coe v0 of
      C_mkregfile_234 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v19
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-t4
d_get'45't4_232 :: T_RegFile_152 -> Integer
d_get'45't4_232 v0
  = case coe v0 of
      C_mkregfile_234 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.readReg
d_readReg_236 ::
  T_RegFile_152 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 -> Integer
d_readReg_236 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_zero_10
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_ra_12
        -> coe d_get'45'ra_194 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14
        -> coe d_get'45'sp_196 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_fp_16
        -> coe d_get'45'fp_198 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18
        -> coe d_get'45'a0_200 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a1_20
        -> coe d_get'45'a1_202 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a2_22
        -> coe d_get'45'a2_204 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a3_24
        -> coe d_get'45'a3_206 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a4_26
        -> coe d_get'45'a4_208 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a5_28
        -> coe d_get'45'a5_210 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a6_30
        -> coe d_get'45'a6_212 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a7_32
        -> coe d_get'45'a7_214 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s1_34
        -> coe d_get'45's1_216 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s2_36
        -> coe d_get'45's2_218 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s3_38
        -> coe d_get'45's3_220 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s4_40
        -> coe d_get'45's4_222 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42
        -> coe d_get'45't0_224 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44
        -> coe d_get'45't1_226 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t2_46
        -> coe d_get'45't2_228 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t3_48
        -> coe d_get'45't3_230 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t4_50
        -> coe d_get'45't4_232 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.writeReg
d_writeReg_280 ::
  T_RegFile_152 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  Integer -> T_RegFile_152
d_writeReg_280 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_zero_10
        -> coe (\ v2 -> v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_ra_12
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_234 (coe v2) (coe d_get'45'sp_196 (coe v0))
                  (coe d_get'45'fp_198 (coe v0)) (coe d_get'45'a0_200 (coe v0))
                  (coe d_get'45'a1_202 (coe v0)) (coe d_get'45'a2_204 (coe v0))
                  (coe d_get'45'a3_206 (coe v0)) (coe d_get'45'a4_208 (coe v0))
                  (coe d_get'45'a5_210 (coe v0)) (coe d_get'45'a6_212 (coe v0))
                  (coe d_get'45'a7_214 (coe v0)) (coe d_get'45's1_216 (coe v0))
                  (coe d_get'45's2_218 (coe v0)) (coe d_get'45's3_220 (coe v0))
                  (coe d_get'45's4_222 (coe v0)) (coe d_get'45't0_224 (coe v0))
                  (coe d_get'45't1_226 (coe v0)) (coe d_get'45't2_228 (coe v0))
                  (coe d_get'45't3_230 (coe v0)) (coe d_get'45't4_232 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_234 (coe d_get'45'ra_194 (coe v0)) (coe v2)
                  (coe d_get'45'fp_198 (coe v0)) (coe d_get'45'a0_200 (coe v0))
                  (coe d_get'45'a1_202 (coe v0)) (coe d_get'45'a2_204 (coe v0))
                  (coe d_get'45'a3_206 (coe v0)) (coe d_get'45'a4_208 (coe v0))
                  (coe d_get'45'a5_210 (coe v0)) (coe d_get'45'a6_212 (coe v0))
                  (coe d_get'45'a7_214 (coe v0)) (coe d_get'45's1_216 (coe v0))
                  (coe d_get'45's2_218 (coe v0)) (coe d_get'45's3_220 (coe v0))
                  (coe d_get'45's4_222 (coe v0)) (coe d_get'45't0_224 (coe v0))
                  (coe d_get'45't1_226 (coe v0)) (coe d_get'45't2_228 (coe v0))
                  (coe d_get'45't3_230 (coe v0)) (coe d_get'45't4_232 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_fp_16
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_234 (coe d_get'45'ra_194 (coe v0))
                  (coe d_get'45'sp_196 (coe v0)) (coe v2)
                  (coe d_get'45'a0_200 (coe v0)) (coe d_get'45'a1_202 (coe v0))
                  (coe d_get'45'a2_204 (coe v0)) (coe d_get'45'a3_206 (coe v0))
                  (coe d_get'45'a4_208 (coe v0)) (coe d_get'45'a5_210 (coe v0))
                  (coe d_get'45'a6_212 (coe v0)) (coe d_get'45'a7_214 (coe v0))
                  (coe d_get'45's1_216 (coe v0)) (coe d_get'45's2_218 (coe v0))
                  (coe d_get'45's3_220 (coe v0)) (coe d_get'45's4_222 (coe v0))
                  (coe d_get'45't0_224 (coe v0)) (coe d_get'45't1_226 (coe v0))
                  (coe d_get'45't2_228 (coe v0)) (coe d_get'45't3_230 (coe v0))
                  (coe d_get'45't4_232 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_234 (coe d_get'45'ra_194 (coe v0))
                  (coe d_get'45'sp_196 (coe v0)) (coe d_get'45'fp_198 (coe v0))
                  (coe v2) (coe d_get'45'a1_202 (coe v0))
                  (coe d_get'45'a2_204 (coe v0)) (coe d_get'45'a3_206 (coe v0))
                  (coe d_get'45'a4_208 (coe v0)) (coe d_get'45'a5_210 (coe v0))
                  (coe d_get'45'a6_212 (coe v0)) (coe d_get'45'a7_214 (coe v0))
                  (coe d_get'45's1_216 (coe v0)) (coe d_get'45's2_218 (coe v0))
                  (coe d_get'45's3_220 (coe v0)) (coe d_get'45's4_222 (coe v0))
                  (coe d_get'45't0_224 (coe v0)) (coe d_get'45't1_226 (coe v0))
                  (coe d_get'45't2_228 (coe v0)) (coe d_get'45't3_230 (coe v0))
                  (coe d_get'45't4_232 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a1_20
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_234 (coe d_get'45'ra_194 (coe v0))
                  (coe d_get'45'sp_196 (coe v0)) (coe d_get'45'fp_198 (coe v0))
                  (coe d_get'45'a0_200 (coe v0)) (coe v2)
                  (coe d_get'45'a2_204 (coe v0)) (coe d_get'45'a3_206 (coe v0))
                  (coe d_get'45'a4_208 (coe v0)) (coe d_get'45'a5_210 (coe v0))
                  (coe d_get'45'a6_212 (coe v0)) (coe d_get'45'a7_214 (coe v0))
                  (coe d_get'45's1_216 (coe v0)) (coe d_get'45's2_218 (coe v0))
                  (coe d_get'45's3_220 (coe v0)) (coe d_get'45's4_222 (coe v0))
                  (coe d_get'45't0_224 (coe v0)) (coe d_get'45't1_226 (coe v0))
                  (coe d_get'45't2_228 (coe v0)) (coe d_get'45't3_230 (coe v0))
                  (coe d_get'45't4_232 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a2_22
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_234 (coe d_get'45'ra_194 (coe v0))
                  (coe d_get'45'sp_196 (coe v0)) (coe d_get'45'fp_198 (coe v0))
                  (coe d_get'45'a0_200 (coe v0)) (coe d_get'45'a1_202 (coe v0))
                  (coe v2) (coe d_get'45'a3_206 (coe v0))
                  (coe d_get'45'a4_208 (coe v0)) (coe d_get'45'a5_210 (coe v0))
                  (coe d_get'45'a6_212 (coe v0)) (coe d_get'45'a7_214 (coe v0))
                  (coe d_get'45's1_216 (coe v0)) (coe d_get'45's2_218 (coe v0))
                  (coe d_get'45's3_220 (coe v0)) (coe d_get'45's4_222 (coe v0))
                  (coe d_get'45't0_224 (coe v0)) (coe d_get'45't1_226 (coe v0))
                  (coe d_get'45't2_228 (coe v0)) (coe d_get'45't3_230 (coe v0))
                  (coe d_get'45't4_232 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a3_24
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_234 (coe d_get'45'ra_194 (coe v0))
                  (coe d_get'45'sp_196 (coe v0)) (coe d_get'45'fp_198 (coe v0))
                  (coe d_get'45'a0_200 (coe v0)) (coe d_get'45'a1_202 (coe v0))
                  (coe d_get'45'a2_204 (coe v0)) (coe v2)
                  (coe d_get'45'a4_208 (coe v0)) (coe d_get'45'a5_210 (coe v0))
                  (coe d_get'45'a6_212 (coe v0)) (coe d_get'45'a7_214 (coe v0))
                  (coe d_get'45's1_216 (coe v0)) (coe d_get'45's2_218 (coe v0))
                  (coe d_get'45's3_220 (coe v0)) (coe d_get'45's4_222 (coe v0))
                  (coe d_get'45't0_224 (coe v0)) (coe d_get'45't1_226 (coe v0))
                  (coe d_get'45't2_228 (coe v0)) (coe d_get'45't3_230 (coe v0))
                  (coe d_get'45't4_232 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a4_26
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_234 (coe d_get'45'ra_194 (coe v0))
                  (coe d_get'45'sp_196 (coe v0)) (coe d_get'45'fp_198 (coe v0))
                  (coe d_get'45'a0_200 (coe v0)) (coe d_get'45'a1_202 (coe v0))
                  (coe d_get'45'a2_204 (coe v0)) (coe d_get'45'a3_206 (coe v0))
                  (coe v2) (coe d_get'45'a5_210 (coe v0))
                  (coe d_get'45'a6_212 (coe v0)) (coe d_get'45'a7_214 (coe v0))
                  (coe d_get'45's1_216 (coe v0)) (coe d_get'45's2_218 (coe v0))
                  (coe d_get'45's3_220 (coe v0)) (coe d_get'45's4_222 (coe v0))
                  (coe d_get'45't0_224 (coe v0)) (coe d_get'45't1_226 (coe v0))
                  (coe d_get'45't2_228 (coe v0)) (coe d_get'45't3_230 (coe v0))
                  (coe d_get'45't4_232 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a5_28
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_234 (coe d_get'45'ra_194 (coe v0))
                  (coe d_get'45'sp_196 (coe v0)) (coe d_get'45'fp_198 (coe v0))
                  (coe d_get'45'a0_200 (coe v0)) (coe d_get'45'a1_202 (coe v0))
                  (coe d_get'45'a2_204 (coe v0)) (coe d_get'45'a3_206 (coe v0))
                  (coe d_get'45'a4_208 (coe v0)) (coe v2)
                  (coe d_get'45'a6_212 (coe v0)) (coe d_get'45'a7_214 (coe v0))
                  (coe d_get'45's1_216 (coe v0)) (coe d_get'45's2_218 (coe v0))
                  (coe d_get'45's3_220 (coe v0)) (coe d_get'45's4_222 (coe v0))
                  (coe d_get'45't0_224 (coe v0)) (coe d_get'45't1_226 (coe v0))
                  (coe d_get'45't2_228 (coe v0)) (coe d_get'45't3_230 (coe v0))
                  (coe d_get'45't4_232 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a6_30
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_234 (coe d_get'45'ra_194 (coe v0))
                  (coe d_get'45'sp_196 (coe v0)) (coe d_get'45'fp_198 (coe v0))
                  (coe d_get'45'a0_200 (coe v0)) (coe d_get'45'a1_202 (coe v0))
                  (coe d_get'45'a2_204 (coe v0)) (coe d_get'45'a3_206 (coe v0))
                  (coe d_get'45'a4_208 (coe v0)) (coe d_get'45'a5_210 (coe v0))
                  (coe v2) (coe d_get'45'a7_214 (coe v0))
                  (coe d_get'45's1_216 (coe v0)) (coe d_get'45's2_218 (coe v0))
                  (coe d_get'45's3_220 (coe v0)) (coe d_get'45's4_222 (coe v0))
                  (coe d_get'45't0_224 (coe v0)) (coe d_get'45't1_226 (coe v0))
                  (coe d_get'45't2_228 (coe v0)) (coe d_get'45't3_230 (coe v0))
                  (coe d_get'45't4_232 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a7_32
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_234 (coe d_get'45'ra_194 (coe v0))
                  (coe d_get'45'sp_196 (coe v0)) (coe d_get'45'fp_198 (coe v0))
                  (coe d_get'45'a0_200 (coe v0)) (coe d_get'45'a1_202 (coe v0))
                  (coe d_get'45'a2_204 (coe v0)) (coe d_get'45'a3_206 (coe v0))
                  (coe d_get'45'a4_208 (coe v0)) (coe d_get'45'a5_210 (coe v0))
                  (coe d_get'45'a6_212 (coe v0)) (coe v2)
                  (coe d_get'45's1_216 (coe v0)) (coe d_get'45's2_218 (coe v0))
                  (coe d_get'45's3_220 (coe v0)) (coe d_get'45's4_222 (coe v0))
                  (coe d_get'45't0_224 (coe v0)) (coe d_get'45't1_226 (coe v0))
                  (coe d_get'45't2_228 (coe v0)) (coe d_get'45't3_230 (coe v0))
                  (coe d_get'45't4_232 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s1_34
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_234 (coe d_get'45'ra_194 (coe v0))
                  (coe d_get'45'sp_196 (coe v0)) (coe d_get'45'fp_198 (coe v0))
                  (coe d_get'45'a0_200 (coe v0)) (coe d_get'45'a1_202 (coe v0))
                  (coe d_get'45'a2_204 (coe v0)) (coe d_get'45'a3_206 (coe v0))
                  (coe d_get'45'a4_208 (coe v0)) (coe d_get'45'a5_210 (coe v0))
                  (coe d_get'45'a6_212 (coe v0)) (coe d_get'45'a7_214 (coe v0))
                  (coe v2) (coe d_get'45's2_218 (coe v0))
                  (coe d_get'45's3_220 (coe v0)) (coe d_get'45's4_222 (coe v0))
                  (coe d_get'45't0_224 (coe v0)) (coe d_get'45't1_226 (coe v0))
                  (coe d_get'45't2_228 (coe v0)) (coe d_get'45't3_230 (coe v0))
                  (coe d_get'45't4_232 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s2_36
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_234 (coe d_get'45'ra_194 (coe v0))
                  (coe d_get'45'sp_196 (coe v0)) (coe d_get'45'fp_198 (coe v0))
                  (coe d_get'45'a0_200 (coe v0)) (coe d_get'45'a1_202 (coe v0))
                  (coe d_get'45'a2_204 (coe v0)) (coe d_get'45'a3_206 (coe v0))
                  (coe d_get'45'a4_208 (coe v0)) (coe d_get'45'a5_210 (coe v0))
                  (coe d_get'45'a6_212 (coe v0)) (coe d_get'45'a7_214 (coe v0))
                  (coe d_get'45's1_216 (coe v0)) (coe v2)
                  (coe d_get'45's3_220 (coe v0)) (coe d_get'45's4_222 (coe v0))
                  (coe d_get'45't0_224 (coe v0)) (coe d_get'45't1_226 (coe v0))
                  (coe d_get'45't2_228 (coe v0)) (coe d_get'45't3_230 (coe v0))
                  (coe d_get'45't4_232 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s3_38
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_234 (coe d_get'45'ra_194 (coe v0))
                  (coe d_get'45'sp_196 (coe v0)) (coe d_get'45'fp_198 (coe v0))
                  (coe d_get'45'a0_200 (coe v0)) (coe d_get'45'a1_202 (coe v0))
                  (coe d_get'45'a2_204 (coe v0)) (coe d_get'45'a3_206 (coe v0))
                  (coe d_get'45'a4_208 (coe v0)) (coe d_get'45'a5_210 (coe v0))
                  (coe d_get'45'a6_212 (coe v0)) (coe d_get'45'a7_214 (coe v0))
                  (coe d_get'45's1_216 (coe v0)) (coe d_get'45's2_218 (coe v0))
                  (coe v2) (coe d_get'45's4_222 (coe v0))
                  (coe d_get'45't0_224 (coe v0)) (coe d_get'45't1_226 (coe v0))
                  (coe d_get'45't2_228 (coe v0)) (coe d_get'45't3_230 (coe v0))
                  (coe d_get'45't4_232 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s4_40
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_234 (coe d_get'45'ra_194 (coe v0))
                  (coe d_get'45'sp_196 (coe v0)) (coe d_get'45'fp_198 (coe v0))
                  (coe d_get'45'a0_200 (coe v0)) (coe d_get'45'a1_202 (coe v0))
                  (coe d_get'45'a2_204 (coe v0)) (coe d_get'45'a3_206 (coe v0))
                  (coe d_get'45'a4_208 (coe v0)) (coe d_get'45'a5_210 (coe v0))
                  (coe d_get'45'a6_212 (coe v0)) (coe d_get'45'a7_214 (coe v0))
                  (coe d_get'45's1_216 (coe v0)) (coe d_get'45's2_218 (coe v0))
                  (coe d_get'45's3_220 (coe v0)) (coe v2)
                  (coe d_get'45't0_224 (coe v0)) (coe d_get'45't1_226 (coe v0))
                  (coe d_get'45't2_228 (coe v0)) (coe d_get'45't3_230 (coe v0))
                  (coe d_get'45't4_232 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_234 (coe d_get'45'ra_194 (coe v0))
                  (coe d_get'45'sp_196 (coe v0)) (coe d_get'45'fp_198 (coe v0))
                  (coe d_get'45'a0_200 (coe v0)) (coe d_get'45'a1_202 (coe v0))
                  (coe d_get'45'a2_204 (coe v0)) (coe d_get'45'a3_206 (coe v0))
                  (coe d_get'45'a4_208 (coe v0)) (coe d_get'45'a5_210 (coe v0))
                  (coe d_get'45'a6_212 (coe v0)) (coe d_get'45'a7_214 (coe v0))
                  (coe d_get'45's1_216 (coe v0)) (coe d_get'45's2_218 (coe v0))
                  (coe d_get'45's3_220 (coe v0)) (coe d_get'45's4_222 (coe v0))
                  (coe v2) (coe d_get'45't1_226 (coe v0))
                  (coe d_get'45't2_228 (coe v0)) (coe d_get'45't3_230 (coe v0))
                  (coe d_get'45't4_232 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_234 (coe d_get'45'ra_194 (coe v0))
                  (coe d_get'45'sp_196 (coe v0)) (coe d_get'45'fp_198 (coe v0))
                  (coe d_get'45'a0_200 (coe v0)) (coe d_get'45'a1_202 (coe v0))
                  (coe d_get'45'a2_204 (coe v0)) (coe d_get'45'a3_206 (coe v0))
                  (coe d_get'45'a4_208 (coe v0)) (coe d_get'45'a5_210 (coe v0))
                  (coe d_get'45'a6_212 (coe v0)) (coe d_get'45'a7_214 (coe v0))
                  (coe d_get'45's1_216 (coe v0)) (coe d_get'45's2_218 (coe v0))
                  (coe d_get'45's3_220 (coe v0)) (coe d_get'45's4_222 (coe v0))
                  (coe d_get'45't0_224 (coe v0)) (coe v2)
                  (coe d_get'45't2_228 (coe v0)) (coe d_get'45't3_230 (coe v0))
                  (coe d_get'45't4_232 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t2_46
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_234 (coe d_get'45'ra_194 (coe v0))
                  (coe d_get'45'sp_196 (coe v0)) (coe d_get'45'fp_198 (coe v0))
                  (coe d_get'45'a0_200 (coe v0)) (coe d_get'45'a1_202 (coe v0))
                  (coe d_get'45'a2_204 (coe v0)) (coe d_get'45'a3_206 (coe v0))
                  (coe d_get'45'a4_208 (coe v0)) (coe d_get'45'a5_210 (coe v0))
                  (coe d_get'45'a6_212 (coe v0)) (coe d_get'45'a7_214 (coe v0))
                  (coe d_get'45's1_216 (coe v0)) (coe d_get'45's2_218 (coe v0))
                  (coe d_get'45's3_220 (coe v0)) (coe d_get'45's4_222 (coe v0))
                  (coe d_get'45't0_224 (coe v0)) (coe d_get'45't1_226 (coe v0))
                  (coe v2) (coe d_get'45't3_230 (coe v0))
                  (coe d_get'45't4_232 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t3_48
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_234 (coe d_get'45'ra_194 (coe v0))
                  (coe d_get'45'sp_196 (coe v0)) (coe d_get'45'fp_198 (coe v0))
                  (coe d_get'45'a0_200 (coe v0)) (coe d_get'45'a1_202 (coe v0))
                  (coe d_get'45'a2_204 (coe v0)) (coe d_get'45'a3_206 (coe v0))
                  (coe d_get'45'a4_208 (coe v0)) (coe d_get'45'a5_210 (coe v0))
                  (coe d_get'45'a6_212 (coe v0)) (coe d_get'45'a7_214 (coe v0))
                  (coe d_get'45's1_216 (coe v0)) (coe d_get'45's2_218 (coe v0))
                  (coe d_get'45's3_220 (coe v0)) (coe d_get'45's4_222 (coe v0))
                  (coe d_get'45't0_224 (coe v0)) (coe d_get'45't1_226 (coe v0))
                  (coe d_get'45't2_228 (coe v0)) (coe v2)
                  (coe d_get'45't4_232 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t4_50
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_234 (coe d_get'45'ra_194 (coe v0))
                  (coe d_get'45'sp_196 (coe v0)) (coe d_get'45'fp_198 (coe v0))
                  (coe d_get'45'a0_200 (coe v0)) (coe d_get'45'a1_202 (coe v0))
                  (coe d_get'45'a2_204 (coe v0)) (coe d_get'45'a3_206 (coe v0))
                  (coe d_get'45'a4_208 (coe v0)) (coe d_get'45'a5_210 (coe v0))
                  (coe d_get'45'a6_212 (coe v0)) (coe d_get'45'a7_214 (coe v0))
                  (coe d_get'45's1_216 (coe v0)) (coe d_get'45's2_218 (coe v0))
                  (coe d_get'45's3_220 (coe v0)) (coe d_get'45's4_222 (coe v0))
                  (coe d_get'45't0_224 (coe v0)) (coe d_get'45't1_226 (coe v0))
                  (coe d_get'45't2_228 (coe v0)) (coe d_get'45't3_230 (coe v0))
                  (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.Addr
d_Addr_366 :: ()
d_Addr_366 = erased
-- Once.CCC.Target.RiscV64.Semantics.Memory
d_Memory_368 :: ()
d_Memory_368 = erased
-- Once.CCC.Target.RiscV64.Semantics.readMem
d_readMem_370 ::
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
d_readMem_370 v0 v1 = coe v0 v1
-- Once.CCC.Target.RiscV64.Semantics.writeMem
d_writeMem_376 ::
  (Integer -> Maybe Integer) ->
  Integer -> Integer -> Integer -> Maybe Integer
d_writeMem_376 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v3) (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
      (coe v0 v3)
-- Once.CCC.Target.RiscV64.Semantics.State
d_State_386 = ()
data T_State_386
  = C_mkstate_404 T_RegFile_152 (Integer -> Maybe Integer) Integer
                  Bool
-- Once.CCC.Target.RiscV64.Semantics.State.regs
d_regs_396 :: T_State_386 -> T_RegFile_152
d_regs_396 v0
  = case coe v0 of
      C_mkstate_404 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.State.memory
d_memory_398 :: T_State_386 -> Integer -> Maybe Integer
d_memory_398 v0
  = case coe v0 of
      C_mkstate_404 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.State.pc
d_pc_400 :: T_State_386 -> Integer
d_pc_400 v0
  = case coe v0 of
      C_mkstate_404 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.State.halted
d_halted_402 :: T_State_386 -> Bool
d_halted_402 v0
  = case coe v0 of
      C_mkstate_404 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.emptyRegFile
d_emptyRegFile_406 :: T_RegFile_152
d_emptyRegFile_406
  = coe
      C_mkregfile_234 (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.emptyMemory
d_emptyMemory_408 :: Integer -> Maybe Integer
d_emptyMemory_408 ~v0 = du_emptyMemory_408
du_emptyMemory_408 :: Maybe Integer
du_emptyMemory_408
  = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.CCC.Target.RiscV64.Semantics.stack-top
d_stack'45'top_412
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Target.RiscV64.Semantics.stack-top"
-- Once.CCC.Target.RiscV64.Semantics.initState
d_initState_414 :: T_State_386
d_initState_414
  = coe
      C_mkstate_404
      (coe
         d_writeReg_280 d_emptyRegFile_406
         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
         d_stack'45'top_412)
      (\ v0 -> coe du_emptyMemory_408) (coe (0 :: Integer))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.CCC.Target.RiscV64.Semantics.effectiveAddr
d_effectiveAddr_416 ::
  T_RegFile_152 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  Integer -> Integer
d_effectiveAddr_416 v0 v1 v2
  = coe addInt (coe d_readReg_236 (coe v0) (coe v1)) (coe v2)
-- Once.CCC.Target.RiscV64.Semantics.effectiveAddrSigned
d_effectiveAddrSigned_424 ::
  T_RegFile_152 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  Integer -> Integer
d_effectiveAddrSigned_424 v0 v1 v2
  = let v3 = d_isNegative_150 (coe v2) in
    coe
      (if coe v3
         then coe
                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                (d_readReg_236 (coe v0) (coe v1))
                (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v2))
         else coe
                addInt (coe d_readReg_236 (coe v0) (coe v1))
                (coe d_offsetToℕ_144 (coe v2)))
-- Once.CCC.Target.RiscV64.Semantics.pcPlusOffset
d_pcPlusOffset_448 :: Integer -> Integer -> Integer
d_pcPlusOffset_448 v0 v1
  = let v2 = d_isNegative_150 (coe v1) in
    coe
      (if coe v2
         then coe
                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0
                (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1))
         else coe addInt (coe d_offsetToℕ_144 (coe v1)) (coe v0))
-- Once.CCC.Target.RiscV64.Semantics.fetch
d_fetch_466 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10
d_fetch_466 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe d_fetch_466 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.find-label-go
d_find'45'label'45'go_474 ::
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  Integer -> Maybe Integer
d_find'45'label'45'go_474 v0 v1 v2
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v3 v4
        -> let v5
                 = d_find'45'label'45'go_474
                     (coe v0) (coe v4) (coe addInt (coe (1 :: Integer)) (coe v2)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_50 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe
                          MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7480'__224 (coe v6)
                          (coe v0))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
                       (coe
                          d_find'45'label'45'go_474 (coe v0) (coe v4)
                          (coe addInt (coe (1 :: Integer)) (coe v2)))
                _ -> coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.find-label
d_find'45'label_492 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 -> Maybe Integer
d_find'45'label_492 v0 v1
  = coe
      d_find'45'label'45'go_474 (coe v1) (coe v0) (coe (0 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.jump-to
d_jump'45'to_498 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  T_State_386 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 -> Maybe T_State_386
d_jump'45'to_498 v0 v1 v2
  = let v3
          = d_find'45'label'45'go_474
              (coe v2) (coe v0) (coe (0 :: Integer)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   C_mkstate_404 (coe d_regs_396 (coe v1)) (coe d_memory_398 (coe v1))
                   (coe v4) (coe d_halted_402 (coe v1)))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   C_mkstate_404 (coe d_regs_396 (coe v1)) (coe d_memory_398 (coe v1))
                   (coe d_pc_400 (coe v1))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Target.RiscV64.Semantics.execInstr
d_execInstr_524 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  T_State_386 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10 ->
  Maybe T_State_386
d_execInstr_524 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12 v3 v4 v5
        -> let v6
                 = coe
                     d_memory_398 v1
                     (d_effectiveAddr_416
                        (coe d_regs_396 (coe v1)) (coe v4) (coe v5)) in
           coe
             (case coe v6 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_404 (coe d_writeReg_280 (d_regs_396 (coe v1)) v3 v7)
                          (coe d_memory_398 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_400 (coe v1)))
                          (coe d_halted_402 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_404 (coe d_regs_396 (coe v1))
                (coe
                   d_writeMem_376 (coe d_memory_398 (coe v1))
                   (coe
                      d_effectiveAddr_416 (coe d_regs_396 (coe v1)) (coe v4) (coe v5))
                   (coe d_readReg_236 (coe d_regs_396 (coe v1)) (coe v3)))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_400 (coe v1)))
                (coe d_halted_402 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_add_16 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_404
                (coe
                   d_writeReg_280 (d_regs_396 (coe v1)) v3
                   (MAlonzo.Code.Once.Word.d__'8853'__26
                      (coe (64 :: Integer))
                      (coe d_readReg_236 (coe d_regs_396 (coe v1)) (coe v4))
                      (coe d_readReg_236 (coe d_regs_396 (coe v1)) (coe v5))))
                (coe d_memory_398 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_400 (coe v1)))
                (coe d_halted_402 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sub_18 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_404
                (coe
                   d_writeReg_280 (d_regs_396 (coe v1)) v3
                   (MAlonzo.Code.Once.Word.d__'8854'__32
                      (coe (64 :: Integer))
                      (coe d_readReg_236 (coe d_regs_396 (coe v1)) (coe v4))
                      (coe d_readReg_236 (coe d_regs_396 (coe v1)) (coe v5))))
                (coe d_memory_398 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_400 (coe v1)))
                (coe d_halted_402 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_404
                (coe
                   d_writeReg_280 (d_regs_396 (coe v1)) v3
                   (MAlonzo.Code.Once.Word.d__'8853'__26
                      (coe (64 :: Integer))
                      (coe d_readReg_236 (coe d_regs_396 (coe v1)) (coe v4))
                      (coe
                         MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer)) (coe v5))))
                (coe d_memory_398 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_400 (coe v1)))
                (coe d_halted_402 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_22 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_404
                (coe
                   d_writeReg_280 (d_regs_396 (coe v1)) v3
                   (MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer)) (coe v4)))
                (coe d_memory_398 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_400 (coe v1)))
                (coe d_halted_402 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_auipc_24 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_404
                (coe
                   d_writeReg_280 (d_regs_396 (coe v1)) v3
                   (addInt
                      (coe d_pc_400 (coe v1))
                      (coe mulInt (coe v4) (coe (4096 :: Integer)))))
                (coe d_memory_398 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_400 (coe v1)))
                (coe d_halted_402 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_lla_26 v3 v4
        -> let v5
                 = d_find'45'label_492
                     (coe v0) (coe MAlonzo.Code.Once.CCC.Label.C_thunk_28 (coe v4)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_404 (coe d_writeReg_280 (d_regs_396 (coe v1)) v3 v6)
                          (coe d_memory_398 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_400 (coe v1)))
                          (coe d_halted_402 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_404 (coe d_regs_396 (coe v1)) (coe d_memory_398 (coe v1))
                          (coe d_pc_400 (coe v1))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_28 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_404
                (coe
                   d_writeReg_280 (d_regs_396 (coe v1)) v3
                   (d_readReg_236 (coe d_regs_396 (coe v1)) (coe v4)))
                (coe d_memory_398 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_400 (coe v1)))
                (coe d_halted_402 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_beq_30 v3 v4 v5
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                eqInt (coe d_readReg_236 (coe d_regs_396 (coe v1)) (coe v3))
                (coe d_readReg_236 (coe d_regs_396 (coe v1)) (coe v4)))
             (coe d_jump'45'to_498 (coe v0) (coe v1) (coe v5))
             (coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   C_mkstate_404 (coe d_regs_396 (coe v1)) (coe d_memory_398 (coe v1))
                   (coe addInt (coe (1 :: Integer)) (coe d_pc_400 (coe v1)))
                   (coe d_halted_402 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_bne_32 v3 v4 v5
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                eqInt (coe d_readReg_236 (coe d_regs_396 (coe v1)) (coe v3))
                (coe d_readReg_236 (coe d_regs_396 (coe v1)) (coe v4)))
             (coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   C_mkstate_404 (coe d_regs_396 (coe v1)) (coe d_memory_398 (coe v1))
                   (coe addInt (coe (1 :: Integer)) (coe d_pc_400 (coe v1)))
                   (coe d_halted_402 (coe v1))))
             (coe d_jump'45'to_498 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_jal_34 v3 v4
        -> coe
             d_jump'45'to_498 (coe v0)
             (coe
                C_mkstate_404
                (coe
                   d_writeReg_280 (d_regs_396 (coe v1)) v3
                   (addInt (coe (1 :: Integer)) (coe d_pc_400 (coe v1))))
                (coe d_memory_398 (coe v1)) (coe d_pc_400 (coe v1))
                (coe d_halted_402 (coe v1)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_jalr_36 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_404
                (coe
                   d_writeReg_280 (d_regs_396 (coe v1)) v3
                   (addInt (coe (1 :: Integer)) (coe d_pc_400 (coe v1))))
                (coe d_memory_398 (coe v1))
                (coe
                   d_effectiveAddr_416 (coe d_regs_396 (coe v1)) (coe v4) (coe v5))
                (coe d_halted_402 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_j_38 v3
        -> coe d_jump'45'to_498 (coe v0) (coe v1) (coe v3)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ret_40
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_404 (coe d_regs_396 (coe v1)) (coe d_memory_398 (coe v1))
                (coe
                   d_readReg_236 (coe d_regs_396 (coe v1))
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_ra_12))
                (coe d_halted_402 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call_42 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_404
                (coe
                   d_writeReg_280 (d_regs_396 (coe v1))
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_ra_12)
                   (addInt (coe (1 :: Integer)) (coe d_pc_400 (coe v1))))
                (coe d_memory_398 (coe v1))
                (coe addInt (coe d_pc_400 (coe v1)) (coe v3))
                (coe d_halted_402 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call'45'sym_44 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_404 (coe d_regs_396 (coe v1)) (coe d_memory_398 (coe v1))
                (coe d_pc_400 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_nop_46
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_404 (coe d_regs_396 (coe v1)) (coe d_memory_398 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_400 (coe v1)))
                (coe d_halted_402 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_unimp_48
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_404 (coe d_regs_396 (coe v1)) (coe d_memory_398 (coe v1))
                (coe d_pc_400 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_50 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_404 (coe d_regs_396 (coe v1)) (coe d_memory_398 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_400 (coe v1)))
                (coe d_halted_402 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.step-not-halted
d_step'45'not'45'halted_746 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  T_State_386 -> Maybe T_State_386
d_step'45'not'45'halted_746 v0 v1
  = let v2 = d_fetch_466 (coe v0) (coe d_pc_400 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe d_execInstr_524 (coe v0) (coe v1) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   C_mkstate_404 (coe d_regs_396 (coe v1)) (coe d_memory_398 (coe v1))
                   (coe d_pc_400 (coe v1))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Target.RiscV64.Semantics.step
d_step_756 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  T_State_386 -> Maybe T_State_386
d_step_756 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_halted_402 (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1))
      (coe d_step'45'not'45'halted_746 (coe v0) (coe v1))
-- Once.CCC.Target.RiscV64.Semantics.exec
d_exec_762 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  T_State_386 -> Maybe T_State_386
d_exec_762 v0 v1 v2
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe d_halted_402 (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
                (coe
                   d_exec'45'cont_764 (coe v3) (coe v1)
                   (coe d_step'45'not'45'halted_746 (coe v1) (coe v2))))
-- Once.CCC.Target.RiscV64.Semantics.exec-cont
d_exec'45'cont_764 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  Maybe T_State_386 -> Maybe T_State_386
d_exec'45'cont_764 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_halted_402 (coe v3)) (coe v2)
             (coe d_exec_762 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.exec-until-pc
d_exec'45'until'45'pc_784 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  T_State_386 -> Maybe T_State_386
d_exec'45'until'45'pc_784 v0 v1 v2 v3
  = case coe v1 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v5 = d_halted_402 (coe v3) in
              coe
                (if coe v5
                   then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
                   else (let v6
                               = coe
                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                   erased
                                   (\ v6 ->
                                      coe
                                        MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                        (coe d_pc_400 (coe v3)))
                                   (coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                      (coe eqInt (coe d_pc_400 (coe v3)) (coe v0))) in
                         coe
                           (case coe v6 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                                -> if coe v7
                                     then coe
                                            seq (coe v8)
                                            (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3))
                                     else coe
                                            seq (coe v8)
                                            (let v9
                                                   = coe
                                                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                       (coe v7)
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                          (coe v3))
                                                       (coe
                                                          d_step'45'not'45'halted_746 (coe v2)
                                                          (coe v3)) in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> coe
                                                         d_exec'45'until'45'pc_784 (coe v0) (coe v4)
                                                         (coe v2) (coe v10)
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> coe v9
                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Target.RiscV64.Semantics.defaultFuel
d_defaultFuel_862 :: Integer
d_defaultFuel_862 = coe (10000 :: Integer)
-- Once.CCC.Target.RiscV64.Semantics.run
d_run_864 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  T_State_386 -> Maybe T_State_386
d_run_864 = coe d_exec_762 (coe d_defaultFuel_862)
