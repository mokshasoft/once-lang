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

module MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax
import qualified MAlonzo.Code.Once.Spec.Word
import qualified MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg
import qualified MAlonzo.Code.Once.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Target.X86-32.Semantics.W._%ˢ_
d__'37''738'__12 :: Integer -> Integer -> Integer
d__'37''738'__12
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'37''738'__122 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W._/ˢ_
d__'47''738'__14 :: Integer -> Integer -> Integer
d__'47''738'__14
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'47''738'__116 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W._<ˢ_
d__'60''738'__16 :: Integer -> Integer -> Bool
d__'60''738'__16
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'60''738'__76 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W._divℕ_
d__divℕ__18 :: Integer -> Integer -> Integer
d__divℕ__18 = coe MAlonzo.Code.Once.Spec.Word.du__divℕ__88
-- Once.CCC.Target.X86-32.Semantics.W._modℕ_
d__modℕ__20 :: Integer -> Integer -> Integer
d__modℕ__20 = coe MAlonzo.Code.Once.Spec.Word.du__modℕ__90
-- Once.CCC.Target.X86-32.Semantics.W._≡ʷ_
d__'8801''695'__22 :: Integer -> Integer -> Bool
d__'8801''695'__22
  = coe MAlonzo.Code.Once.Spec.Word.du__'8801''695'__82
-- Once.CCC.Target.X86-32.Semantics.W._⊕_
d__'8853'__24 :: Integer -> Integer -> Integer
d__'8853'__24
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8853'__28 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W._⊖_
d__'8854'__26 :: Integer -> Integer -> Integer
d__'8854'__26
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8854'__34 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W._⊗_
d__'8855'__28 :: Integer -> Integer -> Integer
d__'8855'__28
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8855'__40 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.InRange
d_InRange_30 :: Integer -> ()
d_InRange_30 = erased
-- Once.CCC.Target.X86-32.Semantics.W.Word
d_Word_32 :: ()
d_Word_32 = erased
-- Once.CCC.Target.X86-32.Semantics.W.fromℤ
d_fromℤ_34 :: Integer -> Integer
d_fromℤ_34
  = coe MAlonzo.Code.Once.Spec.Word.d_fromℤ_22 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.half
d_half_36 :: Integer
d_half_36
  = coe MAlonzo.Code.Once.Spec.Word.d_half_50 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.inRange?
d_inRange'63'_38 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_38
  = coe
      MAlonzo.Code.Once.Spec.Word.d_inRange'63'_66 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.intMin
d_intMin_40 :: Integer
d_intMin_40
  = coe MAlonzo.Code.Once.Spec.Word.d_intMin_56 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.modulus
d_modulus_42 :: Integer
d_modulus_42
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.modulus≢0
d_modulus'8802'0_44 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_44
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus'8802'0_14
      (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.negOne
d_negOne_46 :: Integer
d_negOne_46
  = coe MAlonzo.Code.Once.Spec.Word.d_negOne_58 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.norm
d_norm_48 :: Integer -> Integer
d_norm_48
  = coe MAlonzo.Code.Once.Spec.Word.d_norm_18 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.tdivℤ
d_tdivℤ_50 :: Integer -> Integer -> Integer
d_tdivℤ_50 = coe MAlonzo.Code.Once.Spec.Word.du_tdivℤ_104
-- Once.CCC.Target.X86-32.Semantics.W.tmodℤ
d_tmodℤ_52 :: Integer -> Integer -> Integer
d_tmodℤ_52 = coe MAlonzo.Code.Once.Spec.Word.du_tmodℤ_106
-- Once.CCC.Target.X86-32.Semantics.W.toWord
d_toWord_54 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_54 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Word.du_toWord_72 (coe (32 :: Integer)) v0
-- Once.CCC.Target.X86-32.Semantics.W.toℤ
d_toℤ_56 :: Integer -> Integer
d_toℤ_56
  = coe MAlonzo.Code.Once.Spec.Word.d_toℤ_52 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.⊝_
d_'8861'__58 :: Integer -> Integer
d_'8861'__58
  = coe
      MAlonzo.Code.Once.Spec.Word.d_'8861'__46 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.WL.%ˢ-else
d_'37''738''45'else_62 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_62 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.%ˢ-in-range
d_'37''738''45'in'45'range_64 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_64 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_530
      (coe (32 :: Integer)) v2 v3 v4
-- Once.CCC.Target.X86-32.Semantics.WL.%ˢ-mid
d_'37''738''45'mid_66 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_66 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.%ˢ-negOne
d_'37''738''45'negOne_68 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_68 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.%ˢ-zero
d_'37''738''45'zero_70 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_70 = erased
-- Once.CCC.Target.X86-32.Semantics.WL./ˢ-else
d_'47''738''45'else_72 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_72 = erased
-- Once.CCC.Target.X86-32.Semantics.WL./ˢ-in-range
d_'47''738''45'in'45'range_74 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_74 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_496
      (coe (32 :: Integer)) v2 v3
-- Once.CCC.Target.X86-32.Semantics.WL./ˢ-mid
d_'47''738''45'mid_76 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_76 = erased
-- Once.CCC.Target.X86-32.Semantics.WL./ˢ-negOne
d_'47''738''45'negOne_78 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_78 = erased
-- Once.CCC.Target.X86-32.Semantics.WL./ˢ-pow2
d_'47''738''45'pow2_80 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_80 = erased
-- Once.CCC.Target.X86-32.Semantics.WL./ˢ-zero
d_'47''738''45'zero_82 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_82 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.0<half
d_0'60'half_84 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_84 = coe MAlonzo.Code.Once.Word.du_0'60'half_100
-- Once.CCC.Target.X86-32.Semantics.WL.0<modulus
d_0'60'modulus_86 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_86 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_98
-- Once.CCC.Target.X86-32.Semantics.WL.0<negOne
d_0'60'negOne_88 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_88 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_352 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.WL.1<modulus
d_1'60'modulus_90 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_90
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_722 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.WL.2*n≡n+n
d_2'42'n'8801'n'43'n_92 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_92 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.2≤modulus
d_2'8804'modulus_94 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_94 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_348 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.WL.<⇒<ᵇtrue
d_'60''8658''60''7495'true_96 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8658''60''7495'true_96 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.fromℤ-0
d_fromℤ'45'0_98 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_98 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.fromℤ-in-range
d_fromℤ'45'in'45'range_100 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_100
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_106
      (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.WL.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_102 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_102 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.fromℤ-neg1
d_fromℤ'45'neg1_104 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_104 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.half<modulus
d_half'60'modulus_106 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_106 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_356 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.WL.half≡2^b
d_half'8801'2'94'b_108 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_108 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.half≤negOne
d_half'8804'negOne_110 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_110 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_376
      (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.WL.lit-hi
d_lit'45'hi_112 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'hi_112 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Word.du_lit'45'hi_580 v3
-- Once.CCC.Target.X86-32.Semantics.WL.lit-lo
d_lit'45'lo_114 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'lo_114 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_lit'45'lo_592 (coe (32 :: Integer)) v2 v3
-- Once.CCC.Target.X86-32.Semantics.WL.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_116 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_116 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.mod∸half≡half
d_mod'8760'half'8801'half_118 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_118 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.mod≡half+half
d_mod'8801'half'43'half_120 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_120 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.negOne<modulus
d_negOne'60'modulus_122 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_122 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_364
      (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.WL.negOne≢0
d_negOne'8802'0_124 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_124 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.norm-0
d_norm'45'0_126 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_126 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.norm-id
d_norm'45'id_128 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_128 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.sbb-pos
d_sbb'45'pos_130 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sbb'45'pos_130 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.sbb-zero
d_sbb'45'zero_132 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sbb'45'zero_132 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.sdiv2ᵏ
d_sdiv2'7503'_134 :: Integer -> Integer -> Integer
d_sdiv2'7503'_134
  = coe MAlonzo.Code.Once.Word.d_sdiv2'7503'_70 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.WL.shlᵂ
d_shl'7490'_136 :: Integer -> Integer -> Integer
d_shl'7490'_136
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_64 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.WL.sucNegOne≡mod
d_sucNegOne'8801'mod_138 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_138 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.tdiv-neg1
d_tdiv'45'neg1_140 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_140 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.tmod-neg1
d_tmod'45'neg1_142 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_142 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.toWord≡fromℤ
d_toWord'8801'fromℤ_144 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'8801'fromℤ_144 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.toℤ-negOne
d_toℤ'45'negOne_146 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_146 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.toℤ∘fromℤ
d_toℤ'8728'fromℤ_148 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'8728'fromℤ_148 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.unplus
d_unplus_150 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_unplus_150 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Word.du_unplus_574 v4
-- Once.CCC.Target.X86-32.Semantics.WL.≡ᵇ0-false
d_'8801''7495'0'45'false_152 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_152 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_154 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_154 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.⊕-neg
d_'8853''45'neg_156 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_156 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.⊕-neg-suc
d_'8853''45'neg'45'suc_158 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_158 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.⊕-normʳ
d_'8853''45'norm'691'_160 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_160 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.⊕≡+
d_'8853''8801''43'_162 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_162 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.⊖-normʳ
d_'8854''45'norm'691'_164 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_164 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.⊖-self
d_'8854''45'self_166 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'self_166 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.⊖≡∸
d_'8854''8801''8760'_168 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_168 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.⊗-pow2
d_'8855''45'pow2_170 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_170 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.⊝-fromℤ
d_'8861''45'fromℤ_172 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'fromℤ_172 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.⊝-intMin
d_'8861''45'intMin_174 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_174 = erased
-- Once.CCC.Target.X86-32.Semantics.WL.⊝-invol-norm
d_'8861''45'invol'45'norm_176 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'invol'45'norm_176 = erased
-- Once.CCC.Target.X86-32.Semantics.Word
d_Word_178 :: ()
d_Word_178 = erased
-- Once.CCC.Target.X86-32.Semantics.RegFile
d_RegFile_180 = ()
data T_RegFile_180
  = C_mkregfile_214 Integer Integer Integer Integer Integer Integer
                    Integer Integer
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-eax
d_get'45'eax_198 :: T_RegFile_180 -> Integer
d_get'45'eax_198 v0
  = case coe v0 of
      C_mkregfile_214 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-ebx
d_get'45'ebx_200 :: T_RegFile_180 -> Integer
d_get'45'ebx_200 v0
  = case coe v0 of
      C_mkregfile_214 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-ecx
d_get'45'ecx_202 :: T_RegFile_180 -> Integer
d_get'45'ecx_202 v0
  = case coe v0 of
      C_mkregfile_214 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-edx
d_get'45'edx_204 :: T_RegFile_180 -> Integer
d_get'45'edx_204 v0
  = case coe v0 of
      C_mkregfile_214 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-esi
d_get'45'esi_206 :: T_RegFile_180 -> Integer
d_get'45'esi_206 v0
  = case coe v0 of
      C_mkregfile_214 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-edi
d_get'45'edi_208 :: T_RegFile_180 -> Integer
d_get'45'edi_208 v0
  = case coe v0 of
      C_mkregfile_214 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-ebp
d_get'45'ebp_210 :: T_RegFile_180 -> Integer
d_get'45'ebp_210 v0
  = case coe v0 of
      C_mkregfile_214 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-esp
d_get'45'esp_212 :: T_RegFile_180 -> Integer
d_get'45'esp_212 v0
  = case coe v0 of
      C_mkregfile_214 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.readReg
d_readReg_216 ::
  T_RegFile_180 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer
d_readReg_216 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10
        -> coe d_get'45'eax_198 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebx_12
        -> coe d_get'45'ebx_200 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14
        -> coe d_get'45'ecx_202 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edx_16
        -> coe d_get'45'edx_204 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esi_18
        -> coe d_get'45'esi_206 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edi_20
        -> coe d_get'45'edi_208 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebp_22
        -> coe d_get'45'ebp_210 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24
        -> coe d_get'45'esp_212 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.writeReg
d_writeReg_234 ::
  T_RegFile_180 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  Integer -> T_RegFile_180
d_writeReg_234 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_214 (coe v2) (coe d_get'45'ebx_200 (coe v0))
                  (coe d_get'45'ecx_202 (coe v0)) (coe d_get'45'edx_204 (coe v0))
                  (coe d_get'45'esi_206 (coe v0)) (coe d_get'45'edi_208 (coe v0))
                  (coe d_get'45'ebp_210 (coe v0)) (coe d_get'45'esp_212 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebx_12
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_214 (coe d_get'45'eax_198 (coe v0)) (coe v2)
                  (coe d_get'45'ecx_202 (coe v0)) (coe d_get'45'edx_204 (coe v0))
                  (coe d_get'45'esi_206 (coe v0)) (coe d_get'45'edi_208 (coe v0))
                  (coe d_get'45'ebp_210 (coe v0)) (coe d_get'45'esp_212 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_214 (coe d_get'45'eax_198 (coe v0))
                  (coe d_get'45'ebx_200 (coe v0)) (coe v2)
                  (coe d_get'45'edx_204 (coe v0)) (coe d_get'45'esi_206 (coe v0))
                  (coe d_get'45'edi_208 (coe v0)) (coe d_get'45'ebp_210 (coe v0))
                  (coe d_get'45'esp_212 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edx_16
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_214 (coe d_get'45'eax_198 (coe v0))
                  (coe d_get'45'ebx_200 (coe v0)) (coe d_get'45'ecx_202 (coe v0))
                  (coe v2) (coe d_get'45'esi_206 (coe v0))
                  (coe d_get'45'edi_208 (coe v0)) (coe d_get'45'ebp_210 (coe v0))
                  (coe d_get'45'esp_212 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esi_18
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_214 (coe d_get'45'eax_198 (coe v0))
                  (coe d_get'45'ebx_200 (coe v0)) (coe d_get'45'ecx_202 (coe v0))
                  (coe d_get'45'edx_204 (coe v0)) (coe v2)
                  (coe d_get'45'edi_208 (coe v0)) (coe d_get'45'ebp_210 (coe v0))
                  (coe d_get'45'esp_212 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edi_20
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_214 (coe d_get'45'eax_198 (coe v0))
                  (coe d_get'45'ebx_200 (coe v0)) (coe d_get'45'ecx_202 (coe v0))
                  (coe d_get'45'edx_204 (coe v0)) (coe d_get'45'esi_206 (coe v0))
                  (coe v2) (coe d_get'45'ebp_210 (coe v0))
                  (coe d_get'45'esp_212 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebp_22
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_214 (coe d_get'45'eax_198 (coe v0))
                  (coe d_get'45'ebx_200 (coe v0)) (coe d_get'45'ecx_202 (coe v0))
                  (coe d_get'45'edx_204 (coe v0)) (coe d_get'45'esi_206 (coe v0))
                  (coe d_get'45'edi_208 (coe v0)) (coe v2)
                  (coe d_get'45'esp_212 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_214 (coe d_get'45'eax_198 (coe v0))
                  (coe d_get'45'ebx_200 (coe v0)) (coe d_get'45'ecx_202 (coe v0))
                  (coe d_get'45'edx_204 (coe v0)) (coe d_get'45'esi_206 (coe v0))
                  (coe d_get'45'edi_208 (coe v0)) (coe d_get'45'ebp_210 (coe v0))
                  (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.Addr
d_Addr_268 :: ()
d_Addr_268 = erased
-- Once.CCC.Target.X86-32.Semantics.Memory
d_Memory_270 :: ()
d_Memory_270 = erased
-- Once.CCC.Target.X86-32.Semantics.readMem
d_readMem_272 ::
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
d_readMem_272 v0 v1 = coe v0 v1
-- Once.CCC.Target.X86-32.Semantics.writeMem
d_writeMem_278 ::
  (Integer -> Maybe Integer) ->
  Integer -> Integer -> Integer -> Maybe Integer
d_writeMem_278 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v3) (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
      (coe v0 v3)
-- Once.CCC.Target.X86-32.Semantics.Flags
d_Flags_288 = ()
data T_Flags_288 = C_mkflags_302 Bool Bool Bool
-- Once.CCC.Target.X86-32.Semantics.Flags.zf
d_zf_296 :: T_Flags_288 -> Bool
d_zf_296 v0
  = case coe v0 of
      C_mkflags_302 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.Flags.cf
d_cf_298 :: T_Flags_288 -> Bool
d_cf_298 v0
  = case coe v0 of
      C_mkflags_302 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.Flags.sf
d_sf_300 :: T_Flags_288 -> Bool
d_sf_300 v0
  = case coe v0 of
      C_mkflags_302 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.State
d_State_304 = ()
data T_State_304
  = C_mkstate_326 T_RegFile_180 (Integer -> Maybe Integer)
                  T_Flags_288 Integer Bool
-- Once.CCC.Target.X86-32.Semantics.State.regs
d_regs_316 :: T_State_304 -> T_RegFile_180
d_regs_316 v0
  = case coe v0 of
      C_mkstate_326 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.State.memory
d_memory_318 :: T_State_304 -> Integer -> Maybe Integer
d_memory_318 v0
  = case coe v0 of
      C_mkstate_326 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.State.flags
d_flags_320 :: T_State_304 -> T_Flags_288
d_flags_320 v0
  = case coe v0 of
      C_mkstate_326 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.State.pc
d_pc_322 :: T_State_304 -> Integer
d_pc_322 v0
  = case coe v0 of
      C_mkstate_326 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.State.halted
d_halted_324 :: T_State_304 -> Bool
d_halted_324 v0
  = case coe v0 of
      C_mkstate_326 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.emptyRegFile
d_emptyRegFile_328 :: T_RegFile_180
d_emptyRegFile_328
  = coe
      C_mkregfile_214 (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.emptyMemory
d_emptyMemory_330 :: Integer -> Maybe Integer
d_emptyMemory_330 ~v0 = du_emptyMemory_330
du_emptyMemory_330 :: Maybe Integer
du_emptyMemory_330
  = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.CCC.Target.X86-32.Semantics.initFlags
d_initFlags_334 :: T_Flags_288
d_initFlags_334
  = coe
      C_mkflags_302 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.CCC.Target.X86-32.Semantics.stack-top
d_stack'45'top_336
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Target.X86-32.Semantics.stack-top"
-- Once.CCC.Target.X86-32.Semantics.initStateAt
d_initStateAt_338 :: Integer -> T_State_304
d_initStateAt_338 v0
  = coe
      C_mkstate_326
      (coe
         d_writeReg_234 d_emptyRegFile_328
         (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)
         d_stack'45'top_336)
      (\ v1 -> coe du_emptyMemory_330) (coe d_initFlags_334) (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.CCC.Target.X86-32.Semantics.initState
d_initState_342 :: T_State_304
d_initState_342 = coe d_initStateAt_338 (coe (0 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.effectiveAddr
d_effectiveAddr_344 ::
  T_State_304 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Mem_10 -> Integer
d_effectiveAddr_344 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base_12 v2
        -> coe d_readReg_216 (coe d_regs_316 (coe v0)) (coe v2)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14 v2 v3
        -> coe
             addInt (coe d_readReg_216 (coe d_regs_316 (coe v0)) (coe v2))
             (coe v3)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label'45'rel_16 v2
        -> coe v2
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_abs'45'sym_18 v2
        -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.readOperand
d_readOperand_362 ::
  T_State_304 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Operand_20 ->
  Maybe Integer
d_readOperand_362 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe d_readReg_216 (coe d_regs_316 (coe v0)) (coe v2))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_24 v2
        -> coe
             d_readMem_272 (coe d_memory_318 (coe v0))
             (coe d_effectiveAddr_344 (coe v0) (coe v2))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.Spec.Word.d_norm_18 (coe (32 :: Integer))
                (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.writeOperand
d_writeOperand_376 ::
  T_State_304 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Operand_20 ->
  Integer -> T_State_304
d_writeOperand_376 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkstate_326 (coe d_writeReg_234 (d_regs_316 (coe v0)) v2 v3)
                  (coe d_memory_318 (coe v0)) (coe d_flags_320 (coe v0))
                  (coe d_pc_322 (coe v0)) (coe d_halted_324 (coe v0)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_24 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkstate_326 (coe d_regs_316 (coe v0))
                  (coe
                     d_writeMem_278 (coe d_memory_318 (coe v0))
                     (coe d_effectiveAddr_344 (coe v0) (coe v2)) (coe v3))
                  (coe d_flags_320 (coe v0)) (coe d_pc_322 (coe v0))
                  (coe d_halted_324 (coe v0)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26 v2
        -> coe (\ v3 -> v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.updateFlags
d_updateFlags_392 :: Integer -> T_Flags_288
d_updateFlags_392 v0
  = coe
      C_mkflags_302 (coe eqInt (coe v0) (coe (0 :: Integer)))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.CCC.Target.X86-32.Semantics._<ᵇ_
d__'60''7495'__396 :: Integer -> Integer -> Bool
d__'60''7495'__396 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe (coe d__'60''7495'__396 (coe v2) (coe v3)))
-- Once.CCC.Target.X86-32.Semantics.find-label-go
d_find'45'label'45'go_402 ::
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  Integer -> Maybe Integer
d_find'45'label'45'go_402 v0 v1 v2
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v3 v4
        -> let v5
                 = d_find'45'label'45'go_402
                     (coe v0) (coe v4) (coe addInt (coe (1 :: Integer)) (coe v2)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label_66 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe
                          MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7480'__252 (coe v6)
                          (coe v0))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
                       (coe
                          d_find'45'label'45'go_402 (coe v0) (coe v4)
                          (coe addInt (coe (1 :: Integer)) (coe v2)))
                _ -> coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.find-label
d_find'45'label_420 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 -> Maybe Integer
d_find'45'label_420 v0 v1
  = coe
      d_find'45'label'45'go_402 (coe v1) (coe v0) (coe (0 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.execInstr
d_execInstr_426 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  T_State_304 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28 ->
  Maybe T_State_304
d_execInstr_426 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30 v3 v4
        -> let v5 = d_readOperand_362 (coe v1) (coe v4) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_326 (coe d_regs_316 (coe d_writeOperand_376 v1 v3 v6))
                          (coe d_memory_318 (coe d_writeOperand_376 v1 v3 v6))
                          (coe d_flags_320 (coe d_writeOperand_376 v1 v3 v6))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_322 (coe v1)))
                          (coe d_halted_324 (coe d_writeOperand_376 v1 v3 v6)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_lea_32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_326
                (coe
                   d_writeReg_234 (d_regs_316 (coe v1)) v3
                   (d_effectiveAddr_344 (coe v1) (coe v4)))
                (coe d_memory_318 (coe v1)) (coe d_flags_320 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_322 (coe v1)))
                (coe d_halted_324 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_push_34 v3
        -> let v4 = d_readOperand_362 (coe v1) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_326
                          (coe
                             d_writeReg_234 (d_regs_316 (coe v1))
                             (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_216
                                   (coe d_regs_316 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_74))
                          (coe
                             d_writeMem_278 (coe d_memory_318 (coe v1))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_216
                                   (coe d_regs_316 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_74)
                             (coe v5))
                          (coe d_flags_320 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_322 (coe v1)))
                          (coe d_halted_324 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_pop_36 v3
        -> let v4
                 = d_readMem_272
                     (coe d_memory_318 (coe v1))
                     (coe
                        d_readReg_216 (coe d_regs_316 (coe v1))
                        (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_326
                          (coe
                             d_writeReg_234 (coe d_writeReg_234 (d_regs_316 (coe v1)) v3 v5)
                             (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)
                             (addInt
                                (coe
                                   d_readReg_216 (coe d_regs_316 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_74)))
                          (coe d_memory_318 (coe v1)) (coe d_flags_320 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_322 (coe v1)))
                          (coe d_halted_324 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_add_38 v3 v4
        -> let v5 = d_readOperand_362 (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> let v7 = d_readOperand_362 (coe v1) (coe v4) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_326
                                    (coe
                                       d_regs_316
                                       (coe
                                          d_writeOperand_376 v1 v3
                                          (MAlonzo.Code.Once.Spec.Word.d__'8853'__28
                                             (coe (32 :: Integer)) (coe v6) (coe v8))))
                                    (coe
                                       d_memory_318
                                       (coe
                                          d_writeOperand_376 v1 v3
                                          (MAlonzo.Code.Once.Spec.Word.d__'8853'__28
                                             (coe (32 :: Integer)) (coe v6) (coe v8))))
                                    (coe
                                       d_updateFlags_392
                                       (coe
                                          MAlonzo.Code.Once.Spec.Word.d__'8853'__28
                                          (coe (32 :: Integer)) (coe v6) (coe v8)))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_322 (coe v1)))
                                    (coe
                                       d_halted_324
                                       (coe
                                          d_writeOperand_376 v1 v3
                                          (MAlonzo.Code.Once.Spec.Word.d__'8853'__28
                                             (coe (32 :: Integer)) (coe v6) (coe v8)))))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_sub_40 v3 v4
        -> let v5 = d_readOperand_362 (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> let v7 = d_readOperand_362 (coe v1) (coe v4) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_326
                                    (coe
                                       d_regs_316
                                       (coe
                                          d_writeOperand_376 v1 v3
                                          (MAlonzo.Code.Once.Spec.Word.d__'8854'__34
                                             (coe (32 :: Integer)) (coe v6) (coe v8))))
                                    (coe
                                       d_memory_318
                                       (coe
                                          d_writeOperand_376 v1 v3
                                          (MAlonzo.Code.Once.Spec.Word.d__'8854'__34
                                             (coe (32 :: Integer)) (coe v6) (coe v8))))
                                    (coe
                                       d_updateFlags_392
                                       (coe
                                          MAlonzo.Code.Once.Spec.Word.d__'8854'__34
                                          (coe (32 :: Integer)) (coe v6) (coe v8)))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_322 (coe v1)))
                                    (coe
                                       d_halted_324
                                       (coe
                                          d_writeOperand_376 v1 v3
                                          (MAlonzo.Code.Once.Spec.Word.d__'8854'__34
                                             (coe (32 :: Integer)) (coe v6) (coe v8)))))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_sbb_42 v3 v4
        -> let v5 = d_readOperand_362 (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> let v7 = d_readOperand_362 (coe v1) (coe v4) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_326
                                    (coe
                                       d_regs_316
                                       (coe
                                          d_writeOperand_376 v1 v3
                                          (MAlonzo.Code.Once.Spec.Word.d__'8854'__34
                                             (coe (32 :: Integer))
                                             (coe
                                                MAlonzo.Code.Once.Spec.Word.d__'8854'__34
                                                (coe (32 :: Integer)) (coe v6) (coe v8))
                                             (coe
                                                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                (coe d_cf_298 (coe d_flags_320 (coe v1)))
                                                (coe (1 :: Integer)) (coe (0 :: Integer))))))
                                    (coe
                                       d_memory_318
                                       (coe
                                          d_writeOperand_376 v1 v3
                                          (MAlonzo.Code.Once.Spec.Word.d__'8854'__34
                                             (coe (32 :: Integer))
                                             (coe
                                                MAlonzo.Code.Once.Spec.Word.d__'8854'__34
                                                (coe (32 :: Integer)) (coe v6) (coe v8))
                                             (coe
                                                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                (coe d_cf_298 (coe d_flags_320 (coe v1)))
                                                (coe (1 :: Integer)) (coe (0 :: Integer))))))
                                    (coe
                                       d_updateFlags_392
                                       (coe
                                          MAlonzo.Code.Once.Spec.Word.d__'8854'__34
                                          (coe (32 :: Integer))
                                          (coe
                                             MAlonzo.Code.Once.Spec.Word.d__'8854'__34
                                             (coe (32 :: Integer)) (coe v6) (coe v8))
                                          (coe
                                             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                             (coe d_cf_298 (coe d_flags_320 (coe v1)))
                                             (coe (1 :: Integer)) (coe (0 :: Integer)))))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_322 (coe v1)))
                                    (coe
                                       d_halted_324
                                       (coe
                                          d_writeOperand_376 v1 v3
                                          (MAlonzo.Code.Once.Spec.Word.d__'8854'__34
                                             (coe (32 :: Integer))
                                             (coe
                                                MAlonzo.Code.Once.Spec.Word.d__'8854'__34
                                                (coe (32 :: Integer)) (coe v6) (coe v8))
                                             (coe
                                                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                (coe d_cf_298 (coe d_flags_320 (coe v1)))
                                                (coe (1 :: Integer)) (coe (0 :: Integer)))))))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_cmp_44 v3 v4
        -> let v5 = d_readOperand_362 (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> let v7 = d_readOperand_362 (coe v1) (coe v4) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_326 (coe d_regs_316 (coe v1))
                                    (coe d_memory_318 (coe v1))
                                    (coe
                                       C_mkflags_302 (coe eqInt (coe v6) (coe v8))
                                       (coe d__'60''7495'__396 (coe v6) (coe v8))
                                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_322 (coe v1)))
                                    (coe d_halted_324 (coe v1)))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_test_46 v3 v4
        -> let v5 = d_readOperand_362 (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> let v7 = d_readOperand_362 (coe v1) (coe v4) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_326 (coe d_regs_316 (coe v1))
                                    (coe d_memory_318 (coe v1))
                                    (coe
                                       C_mkflags_302 (coe eqInt (coe v6) (coe (0 :: Integer)))
                                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_322 (coe v1)))
                                    (coe d_halted_324 (coe v1)))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jmp_48 v3
        -> let v4 = d_readOperand_362 (coe v1) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_326 (coe d_regs_316 (coe v1)) (coe d_memory_318 (coe v1))
                          (coe d_flags_320 (coe v1)) (coe v5) (coe d_halted_324 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jne_50 v3
        -> let v4 = d_zf_296 (coe d_flags_320 (coe v1)) in
           coe
             (if coe v4
                then coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_326 (coe d_regs_316 (coe v1)) (coe d_memory_318 (coe v1))
                          (coe d_flags_320 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_322 (coe v1)))
                          (coe d_halted_324 (coe v1)))
                else (let v5 = d_find'45'label_420 (coe v0) (coe v3) in
                      coe
                        (case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                  (coe
                                     C_mkstate_326 (coe d_regs_316 (coe v1))
                                     (coe d_memory_318 (coe v1)) (coe d_flags_320 (coe v1)) (coe v6)
                                     (coe d_halted_324 (coe v1)))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                  (coe
                                     C_mkstate_326 (coe d_regs_316 (coe v1))
                                     (coe d_memory_318 (coe v1)) (coe d_flags_320 (coe v1))
                                     (coe d_pc_322 (coe v1))
                                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_je_52 v3
        -> let v4 = d_zf_296 (coe d_flags_320 (coe v1)) in
           coe
             (if coe v4
                then let v5 = d_find'45'label_420 (coe v0) (coe v3) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_326 (coe d_regs_316 (coe v1))
                                    (coe d_memory_318 (coe v1)) (coe d_flags_320 (coe v1)) (coe v6)
                                    (coe d_halted_324 (coe v1)))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_326 (coe d_regs_316 (coe v1))
                                    (coe d_memory_318 (coe v1)) (coe d_flags_320 (coe v1))
                                    (coe d_pc_322 (coe v1)) (coe v4))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                else coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_326 (coe d_regs_316 (coe v1)) (coe d_memory_318 (coe v1))
                          (coe d_flags_320 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_322 (coe v1)))
                          (coe d_halted_324 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call_54 v3
        -> let v4 = d_readOperand_362 (coe v1) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_326
                          (coe
                             d_writeReg_234 (d_regs_316 (coe v1))
                             (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_216
                                   (coe d_regs_316 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_74))
                          (coe
                             d_writeMem_278 (coe d_memory_318 (coe v1))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_216
                                   (coe d_regs_316 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_74)
                             (coe addInt (coe (1 :: Integer)) (coe d_pc_322 (coe v1))))
                          (coe d_flags_320 (coe v1)) (coe v5) (coe d_halted_324 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call'45'sym_56 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_326 (coe d_regs_316 (coe v1)) (coe d_memory_318 (coe v1))
                (coe d_flags_320 (coe v1)) (coe d_pc_322 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call'45'l_58 v3
        -> let v4 = d_find'45'label_420 (coe v0) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_326
                          (coe
                             d_writeReg_234 (d_regs_316 (coe v1))
                             (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_216
                                   (coe d_regs_316 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_74))
                          (coe
                             d_writeMem_278 (coe d_memory_318 (coe v1))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_216
                                   (coe d_regs_316 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_74)
                             (coe addInt (coe (1 :: Integer)) (coe d_pc_322 (coe v1))))
                          (coe d_flags_320 (coe v1)) (coe v5) (coe d_halted_324 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_326 (coe d_regs_316 (coe v1)) (coe d_memory_318 (coe v1))
                          (coe d_flags_320 (coe v1)) (coe d_pc_322 (coe v1))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ret_60
        -> let v3
                 = d_readMem_272
                     (coe d_memory_318 (coe v1))
                     (coe
                        d_readReg_216 (coe d_regs_316 (coe v1))
                        (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_326
                          (coe
                             d_writeReg_234 (d_regs_316 (coe v1))
                             (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)
                             (addInt
                                (coe
                                   d_readReg_216 (coe d_regs_316 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_74)))
                          (coe d_memory_318 (coe v1)) (coe d_flags_320 (coe v1)) (coe v4)
                          (coe d_halted_324 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_nop_62
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_326 (coe d_regs_316 (coe v1)) (coe d_memory_318 (coe v1))
                (coe d_flags_320 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_322 (coe v1)))
                (coe d_halted_324 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ud2_64
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_326 (coe d_regs_316 (coe v1)) (coe d_memory_318 (coe v1))
                (coe d_flags_320 (coe v1)) (coe d_pc_322 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label_66 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_326 (coe d_regs_316 (coe v1)) (coe d_memory_318 (coe v1))
                (coe d_flags_320 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_322 (coe v1)))
                (coe d_halted_324 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov'45'code_68 v3 v4
        -> let v5
                 = d_find'45'label_420
                     (coe v0)
                     (coe
                        MAlonzo.Code.Once.CCC.Label.C_callee_34
                        (coe MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v4))) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_326 (coe d_writeReg_234 (d_regs_316 (coe v1)) v3 v6)
                          (coe d_memory_318 (coe v1)) (coe d_flags_320 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_322 (coe v1)))
                          (coe d_halted_324 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_326 (coe d_regs_316 (coe v1)) (coe d_memory_318 (coe v1))
                          (coe d_flags_320 (coe v1)) (coe d_pc_322 (coe v1))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jmp'45'l_70 v3
        -> let v4 = d_find'45'label_420 (coe v0) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_326 (coe d_regs_316 (coe v1)) (coe d_memory_318 (coe v1))
                          (coe d_flags_320 (coe v1)) (coe v5) (coe d_halted_324 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_326 (coe d_regs_316 (coe v1)) (coe d_memory_318 (coe v1))
                          (coe d_flags_320 (coe v1)) (coe d_pc_322 (coe v1))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.fetch
d_fetch_700 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28
d_fetch_700 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe d_fetch_700 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.step-not-halted
d_step'45'not'45'halted_708 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  T_State_304 -> Maybe T_State_304
d_step'45'not'45'halted_708 v0 v1
  = let v2 = d_fetch_700 (coe v0) (coe d_pc_322 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe d_execInstr_426 (coe v0) (coe v1) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   C_mkstate_326 (coe d_regs_316 (coe v1)) (coe d_memory_318 (coe v1))
                   (coe d_flags_320 (coe v1)) (coe d_pc_322 (coe v1))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Target.X86-32.Semantics.step
d_step_718 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  T_State_304 -> Maybe T_State_304
d_step_718 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_halted_324 (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1))
      (coe d_step'45'not'45'halted_708 (coe v0) (coe v1))
-- Once.CCC.Target.X86-32.Semantics.exec
d_exec_724 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  T_State_304 -> Maybe T_State_304
d_exec_724 v0 v1 v2
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe d_halted_324 (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
                (coe
                   d_exec'45'cont_726 (coe v3) (coe v1)
                   (coe d_step'45'not'45'halted_708 (coe v1) (coe v2))))
-- Once.CCC.Target.X86-32.Semantics.exec-cont
d_exec'45'cont_726 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  Maybe T_State_304 -> Maybe T_State_304
d_exec'45'cont_726 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_halted_324 (coe v3)) (coe v2)
             (coe d_exec_724 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.defaultFuel
d_defaultFuel_742 :: Integer
d_defaultFuel_742 = coe (10000 :: Integer)
-- Once.CCC.Target.X86-32.Semantics.run
d_run_744 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  T_State_304 -> Maybe T_State_304
d_run_744 = coe d_exec_724 (coe d_defaultFuel_742)
