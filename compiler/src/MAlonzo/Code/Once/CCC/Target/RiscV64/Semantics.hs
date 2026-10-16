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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax
import qualified MAlonzo.Code.Once.Spec.Word
import qualified MAlonzo.Code.Once.Target.RiscV64.PhysReg
import qualified MAlonzo.Code.Once.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Target.RiscV64.Semantics.W._%ˢ_
d__'37''738'__12 :: Integer -> Integer -> Integer
d__'37''738'__12
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'37''738'__122 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W._/ˢ_
d__'47''738'__14 :: Integer -> Integer -> Integer
d__'47''738'__14
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'47''738'__116 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W._<ˢ_
d__'60''738'__16 :: Integer -> Integer -> Bool
d__'60''738'__16
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'60''738'__76 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W._divℕ_
d__divℕ__18 :: Integer -> Integer -> Integer
d__divℕ__18 = coe MAlonzo.Code.Once.Spec.Word.du__divℕ__88
-- Once.CCC.Target.RiscV64.Semantics.W._modℕ_
d__modℕ__20 :: Integer -> Integer -> Integer
d__modℕ__20 = coe MAlonzo.Code.Once.Spec.Word.du__modℕ__90
-- Once.CCC.Target.RiscV64.Semantics.W._≡ʷ_
d__'8801''695'__22 :: Integer -> Integer -> Bool
d__'8801''695'__22
  = coe MAlonzo.Code.Once.Spec.Word.du__'8801''695'__82
-- Once.CCC.Target.RiscV64.Semantics.W._⊕_
d__'8853'__24 :: Integer -> Integer -> Integer
d__'8853'__24
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8853'__28 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W._⊖_
d__'8854'__26 :: Integer -> Integer -> Integer
d__'8854'__26
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8854'__34 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W._⊗_
d__'8855'__28 :: Integer -> Integer -> Integer
d__'8855'__28
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8855'__40 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.InRange
d_InRange_30 :: Integer -> ()
d_InRange_30 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.Word
d_Word_32 :: ()
d_Word_32 = erased
-- Once.CCC.Target.RiscV64.Semantics.W.fromℤ
d_fromℤ_34 :: Integer -> Integer
d_fromℤ_34
  = coe MAlonzo.Code.Once.Spec.Word.d_fromℤ_22 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.half
d_half_36 :: Integer
d_half_36
  = coe MAlonzo.Code.Once.Spec.Word.d_half_50 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.inRange?
d_inRange'63'_38 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_38
  = coe
      MAlonzo.Code.Once.Spec.Word.d_inRange'63'_66 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.intMin
d_intMin_40 :: Integer
d_intMin_40
  = coe MAlonzo.Code.Once.Spec.Word.d_intMin_56 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.modulus
d_modulus_42 :: Integer
d_modulus_42
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.modulus≢0
d_modulus'8802'0_44 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_44
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus'8802'0_14
      (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.negOne
d_negOne_46 :: Integer
d_negOne_46
  = coe MAlonzo.Code.Once.Spec.Word.d_negOne_58 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.norm
d_norm_48 :: Integer -> Integer
d_norm_48
  = coe MAlonzo.Code.Once.Spec.Word.d_norm_18 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.tdivℤ
d_tdivℤ_50 :: Integer -> Integer -> Integer
d_tdivℤ_50 = coe MAlonzo.Code.Once.Spec.Word.du_tdivℤ_104
-- Once.CCC.Target.RiscV64.Semantics.W.tmodℤ
d_tmodℤ_52 :: Integer -> Integer -> Integer
d_tmodℤ_52 = coe MAlonzo.Code.Once.Spec.Word.du_tmodℤ_106
-- Once.CCC.Target.RiscV64.Semantics.W.toWord
d_toWord_54 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_54 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Word.du_toWord_72 (coe (64 :: Integer)) v0
-- Once.CCC.Target.RiscV64.Semantics.W.toℤ
d_toℤ_56 :: Integer -> Integer
d_toℤ_56
  = coe MAlonzo.Code.Once.Spec.Word.d_toℤ_52 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.W.⊝_
d_'8861'__58 :: Integer -> Integer
d_'8861'__58
  = coe
      MAlonzo.Code.Once.Spec.Word.d_'8861'__46 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.WL.%ˢ-else
d_'37''738''45'else_62 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_62 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.%ˢ-in-range
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
      (coe (64 :: Integer)) v2 v3 v4
-- Once.CCC.Target.RiscV64.Semantics.WL.%ˢ-mid
d_'37''738''45'mid_66 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_66 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.%ˢ-negOne
d_'37''738''45'negOne_68 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_68 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.%ˢ-zero
d_'37''738''45'zero_70 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_70 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL./ˢ-else
d_'47''738''45'else_72 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_72 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL./ˢ-in-range
d_'47''738''45'in'45'range_74 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_74 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_496
      (coe (64 :: Integer)) v2 v3
-- Once.CCC.Target.RiscV64.Semantics.WL./ˢ-mid
d_'47''738''45'mid_76 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_76 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL./ˢ-negOne
d_'47''738''45'negOne_78 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_78 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL./ˢ-pow2
d_'47''738''45'pow2_80 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_80 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL./ˢ-zero
d_'47''738''45'zero_82 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_82 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.0<half
d_0'60'half_84 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_84 = coe MAlonzo.Code.Once.Word.du_0'60'half_100
-- Once.CCC.Target.RiscV64.Semantics.WL.0<modulus
d_0'60'modulus_86 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_86 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_98
-- Once.CCC.Target.RiscV64.Semantics.WL.0<negOne
d_0'60'negOne_88 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_88 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_352 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.WL.1<modulus
d_1'60'modulus_90 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_90
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_722 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.WL.2*n≡n+n
d_2'42'n'8801'n'43'n_92 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_92 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.2≤modulus
d_2'8804'modulus_94 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_94 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_348 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.WL.<⇒<ᵇtrue
d_'60''8658''60''7495'true_96 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8658''60''7495'true_96 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.fromℤ-0
d_fromℤ'45'0_98 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_98 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.fromℤ-in-range
d_fromℤ'45'in'45'range_100 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_100
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_106
      (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.WL.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_102 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_102 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.fromℤ-neg1
d_fromℤ'45'neg1_104 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_104 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.half<modulus
d_half'60'modulus_106 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_106 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_356 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.WL.half≡2^b
d_half'8801'2'94'b_108 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_108 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.half≤negOne
d_half'8804'negOne_110 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_110 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_376
      (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.WL.lit-hi
d_lit'45'hi_112 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'hi_112 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Word.du_lit'45'hi_580 v3
-- Once.CCC.Target.RiscV64.Semantics.WL.lit-lo
d_lit'45'lo_114 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'lo_114 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_lit'45'lo_592 (coe (64 :: Integer)) v2 v3
-- Once.CCC.Target.RiscV64.Semantics.WL.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_116 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_116 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.mod∸half≡half
d_mod'8760'half'8801'half_118 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_118 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.mod≡half+half
d_mod'8801'half'43'half_120 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_120 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.negOne<modulus
d_negOne'60'modulus_122 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_122 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_364
      (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.WL.negOne≢0
d_negOne'8802'0_124 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_124 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.norm-0
d_norm'45'0_126 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_126 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.norm-id
d_norm'45'id_128 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_128 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.sbb-pos
d_sbb'45'pos_130 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sbb'45'pos_130 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.sbb-zero
d_sbb'45'zero_132 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sbb'45'zero_132 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.sdiv2ᵏ
d_sdiv2'7503'_134 :: Integer -> Integer -> Integer
d_sdiv2'7503'_134
  = coe MAlonzo.Code.Once.Word.d_sdiv2'7503'_70 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.WL.shlᵂ
d_shl'7490'_136 :: Integer -> Integer -> Integer
d_shl'7490'_136
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_64 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.WL.sucNegOne≡mod
d_sucNegOne'8801'mod_138 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_138 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.tdiv-neg1
d_tdiv'45'neg1_140 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_140 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.tmod-neg1
d_tmod'45'neg1_142 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_142 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.toWord≡fromℤ
d_toWord'8801'fromℤ_144 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'8801'fromℤ_144 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.toℤ-negOne
d_toℤ'45'negOne_146 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_146 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.toℤ∘fromℤ
d_toℤ'8728'fromℤ_148 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'8728'fromℤ_148 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.unplus
d_unplus_150 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_unplus_150 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Word.du_unplus_574 v4
-- Once.CCC.Target.RiscV64.Semantics.WL.≡ᵇ0-false
d_'8801''7495'0'45'false_152 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_152 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_154 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_154 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.⊕-neg
d_'8853''45'neg_156 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_156 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.⊕-neg-suc
d_'8853''45'neg'45'suc_158 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_158 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.⊕-normʳ
d_'8853''45'norm'691'_160 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_160 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.⊕≡+
d_'8853''8801''43'_162 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_162 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.⊖-normʳ
d_'8854''45'norm'691'_164 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_164 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.⊖-self
d_'8854''45'self_166 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'self_166 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.⊖≡∸
d_'8854''8801''8760'_168 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_168 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.⊗-pow2
d_'8855''45'pow2_170 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_170 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.⊝-fromℤ
d_'8861''45'fromℤ_172 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'fromℤ_172 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.⊝-intMin
d_'8861''45'intMin_174 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_174 = erased
-- Once.CCC.Target.RiscV64.Semantics.WL.⊝-invol-norm
d_'8861''45'invol'45'norm_176 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'invol'45'norm_176 = erased
-- Once.CCC.Target.RiscV64.Semantics.Word
d_Word_178 :: ()
d_Word_178 = erased
-- Once.CCC.Target.RiscV64.Semantics.offsetToℕ
d_offsetToℕ_180 :: Integer -> Integer
d_offsetToℕ_180 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) -> coe v0
      _ -> coe (0 :: Integer)
-- Once.CCC.Target.RiscV64.Semantics.isNegative
d_isNegative_186 :: Integer -> Bool
d_isNegative_186 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
-- Once.CCC.Target.RiscV64.Semantics.RegFile
d_RegFile_188 = ()
data T_RegFile_188
  = C_mkregfile_270 Integer Integer Integer Integer Integer Integer
                    Integer Integer Integer Integer Integer Integer Integer Integer
                    Integer Integer Integer Integer Integer Integer
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-ra
d_get'45'ra_230 :: T_RegFile_188 -> Integer
d_get'45'ra_230 v0
  = case coe v0 of
      C_mkregfile_270 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-sp
d_get'45'sp_232 :: T_RegFile_188 -> Integer
d_get'45'sp_232 v0
  = case coe v0 of
      C_mkregfile_270 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-fp
d_get'45'fp_234 :: T_RegFile_188 -> Integer
d_get'45'fp_234 v0
  = case coe v0 of
      C_mkregfile_270 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a0
d_get'45'a0_236 :: T_RegFile_188 -> Integer
d_get'45'a0_236 v0
  = case coe v0 of
      C_mkregfile_270 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a1
d_get'45'a1_238 :: T_RegFile_188 -> Integer
d_get'45'a1_238 v0
  = case coe v0 of
      C_mkregfile_270 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a2
d_get'45'a2_240 :: T_RegFile_188 -> Integer
d_get'45'a2_240 v0
  = case coe v0 of
      C_mkregfile_270 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a3
d_get'45'a3_242 :: T_RegFile_188 -> Integer
d_get'45'a3_242 v0
  = case coe v0 of
      C_mkregfile_270 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a4
d_get'45'a4_244 :: T_RegFile_188 -> Integer
d_get'45'a4_244 v0
  = case coe v0 of
      C_mkregfile_270 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a5
d_get'45'a5_246 :: T_RegFile_188 -> Integer
d_get'45'a5_246 v0
  = case coe v0 of
      C_mkregfile_270 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a6
d_get'45'a6_248 :: T_RegFile_188 -> Integer
d_get'45'a6_248 v0
  = case coe v0 of
      C_mkregfile_270 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a7
d_get'45'a7_250 :: T_RegFile_188 -> Integer
d_get'45'a7_250 v0
  = case coe v0 of
      C_mkregfile_270 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-s1
d_get'45's1_252 :: T_RegFile_188 -> Integer
d_get'45's1_252 v0
  = case coe v0 of
      C_mkregfile_270 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-s2
d_get'45's2_254 :: T_RegFile_188 -> Integer
d_get'45's2_254 v0
  = case coe v0 of
      C_mkregfile_270 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-s3
d_get'45's3_256 :: T_RegFile_188 -> Integer
d_get'45's3_256 v0
  = case coe v0 of
      C_mkregfile_270 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-s4
d_get'45's4_258 :: T_RegFile_188 -> Integer
d_get'45's4_258 v0
  = case coe v0 of
      C_mkregfile_270 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-t0
d_get'45't0_260 :: T_RegFile_188 -> Integer
d_get'45't0_260 v0
  = case coe v0 of
      C_mkregfile_270 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-t1
d_get'45't1_262 :: T_RegFile_188 -> Integer
d_get'45't1_262 v0
  = case coe v0 of
      C_mkregfile_270 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v17
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-t2
d_get'45't2_264 :: T_RegFile_188 -> Integer
d_get'45't2_264 v0
  = case coe v0 of
      C_mkregfile_270 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-t3
d_get'45't3_266 :: T_RegFile_188 -> Integer
d_get'45't3_266 v0
  = case coe v0 of
      C_mkregfile_270 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v19
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-t4
d_get'45't4_268 :: T_RegFile_188 -> Integer
d_get'45't4_268 v0
  = case coe v0 of
      C_mkregfile_270 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.readReg
d_readReg_272 ::
  T_RegFile_188 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 -> Integer
d_readReg_272 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_zero_10
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_ra_12
        -> coe d_get'45'ra_230 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14
        -> coe d_get'45'sp_232 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_fp_16
        -> coe d_get'45'fp_234 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18
        -> coe d_get'45'a0_236 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a1_20
        -> coe d_get'45'a1_238 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a2_22
        -> coe d_get'45'a2_240 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a3_24
        -> coe d_get'45'a3_242 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a4_26
        -> coe d_get'45'a4_244 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a5_28
        -> coe d_get'45'a5_246 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a6_30
        -> coe d_get'45'a6_248 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a7_32
        -> coe d_get'45'a7_250 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s1_34
        -> coe d_get'45's1_252 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s2_36
        -> coe d_get'45's2_254 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s3_38
        -> coe d_get'45's3_256 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s4_40
        -> coe d_get'45's4_258 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42
        -> coe d_get'45't0_260 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44
        -> coe d_get'45't1_262 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t2_46
        -> coe d_get'45't2_264 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t3_48
        -> coe d_get'45't3_266 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t4_50
        -> coe d_get'45't4_268 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.writeReg
d_writeReg_316 ::
  T_RegFile_188 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  Integer -> T_RegFile_188
d_writeReg_316 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_zero_10
        -> coe (\ v2 -> v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_ra_12
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_270 (coe v2) (coe d_get'45'sp_232 (coe v0))
                  (coe d_get'45'fp_234 (coe v0)) (coe d_get'45'a0_236 (coe v0))
                  (coe d_get'45'a1_238 (coe v0)) (coe d_get'45'a2_240 (coe v0))
                  (coe d_get'45'a3_242 (coe v0)) (coe d_get'45'a4_244 (coe v0))
                  (coe d_get'45'a5_246 (coe v0)) (coe d_get'45'a6_248 (coe v0))
                  (coe d_get'45'a7_250 (coe v0)) (coe d_get'45's1_252 (coe v0))
                  (coe d_get'45's2_254 (coe v0)) (coe d_get'45's3_256 (coe v0))
                  (coe d_get'45's4_258 (coe v0)) (coe d_get'45't0_260 (coe v0))
                  (coe d_get'45't1_262 (coe v0)) (coe d_get'45't2_264 (coe v0))
                  (coe d_get'45't3_266 (coe v0)) (coe d_get'45't4_268 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_270 (coe d_get'45'ra_230 (coe v0)) (coe v2)
                  (coe d_get'45'fp_234 (coe v0)) (coe d_get'45'a0_236 (coe v0))
                  (coe d_get'45'a1_238 (coe v0)) (coe d_get'45'a2_240 (coe v0))
                  (coe d_get'45'a3_242 (coe v0)) (coe d_get'45'a4_244 (coe v0))
                  (coe d_get'45'a5_246 (coe v0)) (coe d_get'45'a6_248 (coe v0))
                  (coe d_get'45'a7_250 (coe v0)) (coe d_get'45's1_252 (coe v0))
                  (coe d_get'45's2_254 (coe v0)) (coe d_get'45's3_256 (coe v0))
                  (coe d_get'45's4_258 (coe v0)) (coe d_get'45't0_260 (coe v0))
                  (coe d_get'45't1_262 (coe v0)) (coe d_get'45't2_264 (coe v0))
                  (coe d_get'45't3_266 (coe v0)) (coe d_get'45't4_268 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_fp_16
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_270 (coe d_get'45'ra_230 (coe v0))
                  (coe d_get'45'sp_232 (coe v0)) (coe v2)
                  (coe d_get'45'a0_236 (coe v0)) (coe d_get'45'a1_238 (coe v0))
                  (coe d_get'45'a2_240 (coe v0)) (coe d_get'45'a3_242 (coe v0))
                  (coe d_get'45'a4_244 (coe v0)) (coe d_get'45'a5_246 (coe v0))
                  (coe d_get'45'a6_248 (coe v0)) (coe d_get'45'a7_250 (coe v0))
                  (coe d_get'45's1_252 (coe v0)) (coe d_get'45's2_254 (coe v0))
                  (coe d_get'45's3_256 (coe v0)) (coe d_get'45's4_258 (coe v0))
                  (coe d_get'45't0_260 (coe v0)) (coe d_get'45't1_262 (coe v0))
                  (coe d_get'45't2_264 (coe v0)) (coe d_get'45't3_266 (coe v0))
                  (coe d_get'45't4_268 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_270 (coe d_get'45'ra_230 (coe v0))
                  (coe d_get'45'sp_232 (coe v0)) (coe d_get'45'fp_234 (coe v0))
                  (coe v2) (coe d_get'45'a1_238 (coe v0))
                  (coe d_get'45'a2_240 (coe v0)) (coe d_get'45'a3_242 (coe v0))
                  (coe d_get'45'a4_244 (coe v0)) (coe d_get'45'a5_246 (coe v0))
                  (coe d_get'45'a6_248 (coe v0)) (coe d_get'45'a7_250 (coe v0))
                  (coe d_get'45's1_252 (coe v0)) (coe d_get'45's2_254 (coe v0))
                  (coe d_get'45's3_256 (coe v0)) (coe d_get'45's4_258 (coe v0))
                  (coe d_get'45't0_260 (coe v0)) (coe d_get'45't1_262 (coe v0))
                  (coe d_get'45't2_264 (coe v0)) (coe d_get'45't3_266 (coe v0))
                  (coe d_get'45't4_268 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a1_20
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_270 (coe d_get'45'ra_230 (coe v0))
                  (coe d_get'45'sp_232 (coe v0)) (coe d_get'45'fp_234 (coe v0))
                  (coe d_get'45'a0_236 (coe v0)) (coe v2)
                  (coe d_get'45'a2_240 (coe v0)) (coe d_get'45'a3_242 (coe v0))
                  (coe d_get'45'a4_244 (coe v0)) (coe d_get'45'a5_246 (coe v0))
                  (coe d_get'45'a6_248 (coe v0)) (coe d_get'45'a7_250 (coe v0))
                  (coe d_get'45's1_252 (coe v0)) (coe d_get'45's2_254 (coe v0))
                  (coe d_get'45's3_256 (coe v0)) (coe d_get'45's4_258 (coe v0))
                  (coe d_get'45't0_260 (coe v0)) (coe d_get'45't1_262 (coe v0))
                  (coe d_get'45't2_264 (coe v0)) (coe d_get'45't3_266 (coe v0))
                  (coe d_get'45't4_268 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a2_22
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_270 (coe d_get'45'ra_230 (coe v0))
                  (coe d_get'45'sp_232 (coe v0)) (coe d_get'45'fp_234 (coe v0))
                  (coe d_get'45'a0_236 (coe v0)) (coe d_get'45'a1_238 (coe v0))
                  (coe v2) (coe d_get'45'a3_242 (coe v0))
                  (coe d_get'45'a4_244 (coe v0)) (coe d_get'45'a5_246 (coe v0))
                  (coe d_get'45'a6_248 (coe v0)) (coe d_get'45'a7_250 (coe v0))
                  (coe d_get'45's1_252 (coe v0)) (coe d_get'45's2_254 (coe v0))
                  (coe d_get'45's3_256 (coe v0)) (coe d_get'45's4_258 (coe v0))
                  (coe d_get'45't0_260 (coe v0)) (coe d_get'45't1_262 (coe v0))
                  (coe d_get'45't2_264 (coe v0)) (coe d_get'45't3_266 (coe v0))
                  (coe d_get'45't4_268 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a3_24
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_270 (coe d_get'45'ra_230 (coe v0))
                  (coe d_get'45'sp_232 (coe v0)) (coe d_get'45'fp_234 (coe v0))
                  (coe d_get'45'a0_236 (coe v0)) (coe d_get'45'a1_238 (coe v0))
                  (coe d_get'45'a2_240 (coe v0)) (coe v2)
                  (coe d_get'45'a4_244 (coe v0)) (coe d_get'45'a5_246 (coe v0))
                  (coe d_get'45'a6_248 (coe v0)) (coe d_get'45'a7_250 (coe v0))
                  (coe d_get'45's1_252 (coe v0)) (coe d_get'45's2_254 (coe v0))
                  (coe d_get'45's3_256 (coe v0)) (coe d_get'45's4_258 (coe v0))
                  (coe d_get'45't0_260 (coe v0)) (coe d_get'45't1_262 (coe v0))
                  (coe d_get'45't2_264 (coe v0)) (coe d_get'45't3_266 (coe v0))
                  (coe d_get'45't4_268 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a4_26
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_270 (coe d_get'45'ra_230 (coe v0))
                  (coe d_get'45'sp_232 (coe v0)) (coe d_get'45'fp_234 (coe v0))
                  (coe d_get'45'a0_236 (coe v0)) (coe d_get'45'a1_238 (coe v0))
                  (coe d_get'45'a2_240 (coe v0)) (coe d_get'45'a3_242 (coe v0))
                  (coe v2) (coe d_get'45'a5_246 (coe v0))
                  (coe d_get'45'a6_248 (coe v0)) (coe d_get'45'a7_250 (coe v0))
                  (coe d_get'45's1_252 (coe v0)) (coe d_get'45's2_254 (coe v0))
                  (coe d_get'45's3_256 (coe v0)) (coe d_get'45's4_258 (coe v0))
                  (coe d_get'45't0_260 (coe v0)) (coe d_get'45't1_262 (coe v0))
                  (coe d_get'45't2_264 (coe v0)) (coe d_get'45't3_266 (coe v0))
                  (coe d_get'45't4_268 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a5_28
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_270 (coe d_get'45'ra_230 (coe v0))
                  (coe d_get'45'sp_232 (coe v0)) (coe d_get'45'fp_234 (coe v0))
                  (coe d_get'45'a0_236 (coe v0)) (coe d_get'45'a1_238 (coe v0))
                  (coe d_get'45'a2_240 (coe v0)) (coe d_get'45'a3_242 (coe v0))
                  (coe d_get'45'a4_244 (coe v0)) (coe v2)
                  (coe d_get'45'a6_248 (coe v0)) (coe d_get'45'a7_250 (coe v0))
                  (coe d_get'45's1_252 (coe v0)) (coe d_get'45's2_254 (coe v0))
                  (coe d_get'45's3_256 (coe v0)) (coe d_get'45's4_258 (coe v0))
                  (coe d_get'45't0_260 (coe v0)) (coe d_get'45't1_262 (coe v0))
                  (coe d_get'45't2_264 (coe v0)) (coe d_get'45't3_266 (coe v0))
                  (coe d_get'45't4_268 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a6_30
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_270 (coe d_get'45'ra_230 (coe v0))
                  (coe d_get'45'sp_232 (coe v0)) (coe d_get'45'fp_234 (coe v0))
                  (coe d_get'45'a0_236 (coe v0)) (coe d_get'45'a1_238 (coe v0))
                  (coe d_get'45'a2_240 (coe v0)) (coe d_get'45'a3_242 (coe v0))
                  (coe d_get'45'a4_244 (coe v0)) (coe d_get'45'a5_246 (coe v0))
                  (coe v2) (coe d_get'45'a7_250 (coe v0))
                  (coe d_get'45's1_252 (coe v0)) (coe d_get'45's2_254 (coe v0))
                  (coe d_get'45's3_256 (coe v0)) (coe d_get'45's4_258 (coe v0))
                  (coe d_get'45't0_260 (coe v0)) (coe d_get'45't1_262 (coe v0))
                  (coe d_get'45't2_264 (coe v0)) (coe d_get'45't3_266 (coe v0))
                  (coe d_get'45't4_268 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a7_32
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_270 (coe d_get'45'ra_230 (coe v0))
                  (coe d_get'45'sp_232 (coe v0)) (coe d_get'45'fp_234 (coe v0))
                  (coe d_get'45'a0_236 (coe v0)) (coe d_get'45'a1_238 (coe v0))
                  (coe d_get'45'a2_240 (coe v0)) (coe d_get'45'a3_242 (coe v0))
                  (coe d_get'45'a4_244 (coe v0)) (coe d_get'45'a5_246 (coe v0))
                  (coe d_get'45'a6_248 (coe v0)) (coe v2)
                  (coe d_get'45's1_252 (coe v0)) (coe d_get'45's2_254 (coe v0))
                  (coe d_get'45's3_256 (coe v0)) (coe d_get'45's4_258 (coe v0))
                  (coe d_get'45't0_260 (coe v0)) (coe d_get'45't1_262 (coe v0))
                  (coe d_get'45't2_264 (coe v0)) (coe d_get'45't3_266 (coe v0))
                  (coe d_get'45't4_268 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s1_34
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_270 (coe d_get'45'ra_230 (coe v0))
                  (coe d_get'45'sp_232 (coe v0)) (coe d_get'45'fp_234 (coe v0))
                  (coe d_get'45'a0_236 (coe v0)) (coe d_get'45'a1_238 (coe v0))
                  (coe d_get'45'a2_240 (coe v0)) (coe d_get'45'a3_242 (coe v0))
                  (coe d_get'45'a4_244 (coe v0)) (coe d_get'45'a5_246 (coe v0))
                  (coe d_get'45'a6_248 (coe v0)) (coe d_get'45'a7_250 (coe v0))
                  (coe v2) (coe d_get'45's2_254 (coe v0))
                  (coe d_get'45's3_256 (coe v0)) (coe d_get'45's4_258 (coe v0))
                  (coe d_get'45't0_260 (coe v0)) (coe d_get'45't1_262 (coe v0))
                  (coe d_get'45't2_264 (coe v0)) (coe d_get'45't3_266 (coe v0))
                  (coe d_get'45't4_268 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s2_36
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_270 (coe d_get'45'ra_230 (coe v0))
                  (coe d_get'45'sp_232 (coe v0)) (coe d_get'45'fp_234 (coe v0))
                  (coe d_get'45'a0_236 (coe v0)) (coe d_get'45'a1_238 (coe v0))
                  (coe d_get'45'a2_240 (coe v0)) (coe d_get'45'a3_242 (coe v0))
                  (coe d_get'45'a4_244 (coe v0)) (coe d_get'45'a5_246 (coe v0))
                  (coe d_get'45'a6_248 (coe v0)) (coe d_get'45'a7_250 (coe v0))
                  (coe d_get'45's1_252 (coe v0)) (coe v2)
                  (coe d_get'45's3_256 (coe v0)) (coe d_get'45's4_258 (coe v0))
                  (coe d_get'45't0_260 (coe v0)) (coe d_get'45't1_262 (coe v0))
                  (coe d_get'45't2_264 (coe v0)) (coe d_get'45't3_266 (coe v0))
                  (coe d_get'45't4_268 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s3_38
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_270 (coe d_get'45'ra_230 (coe v0))
                  (coe d_get'45'sp_232 (coe v0)) (coe d_get'45'fp_234 (coe v0))
                  (coe d_get'45'a0_236 (coe v0)) (coe d_get'45'a1_238 (coe v0))
                  (coe d_get'45'a2_240 (coe v0)) (coe d_get'45'a3_242 (coe v0))
                  (coe d_get'45'a4_244 (coe v0)) (coe d_get'45'a5_246 (coe v0))
                  (coe d_get'45'a6_248 (coe v0)) (coe d_get'45'a7_250 (coe v0))
                  (coe d_get'45's1_252 (coe v0)) (coe d_get'45's2_254 (coe v0))
                  (coe v2) (coe d_get'45's4_258 (coe v0))
                  (coe d_get'45't0_260 (coe v0)) (coe d_get'45't1_262 (coe v0))
                  (coe d_get'45't2_264 (coe v0)) (coe d_get'45't3_266 (coe v0))
                  (coe d_get'45't4_268 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s4_40
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_270 (coe d_get'45'ra_230 (coe v0))
                  (coe d_get'45'sp_232 (coe v0)) (coe d_get'45'fp_234 (coe v0))
                  (coe d_get'45'a0_236 (coe v0)) (coe d_get'45'a1_238 (coe v0))
                  (coe d_get'45'a2_240 (coe v0)) (coe d_get'45'a3_242 (coe v0))
                  (coe d_get'45'a4_244 (coe v0)) (coe d_get'45'a5_246 (coe v0))
                  (coe d_get'45'a6_248 (coe v0)) (coe d_get'45'a7_250 (coe v0))
                  (coe d_get'45's1_252 (coe v0)) (coe d_get'45's2_254 (coe v0))
                  (coe d_get'45's3_256 (coe v0)) (coe v2)
                  (coe d_get'45't0_260 (coe v0)) (coe d_get'45't1_262 (coe v0))
                  (coe d_get'45't2_264 (coe v0)) (coe d_get'45't3_266 (coe v0))
                  (coe d_get'45't4_268 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_270 (coe d_get'45'ra_230 (coe v0))
                  (coe d_get'45'sp_232 (coe v0)) (coe d_get'45'fp_234 (coe v0))
                  (coe d_get'45'a0_236 (coe v0)) (coe d_get'45'a1_238 (coe v0))
                  (coe d_get'45'a2_240 (coe v0)) (coe d_get'45'a3_242 (coe v0))
                  (coe d_get'45'a4_244 (coe v0)) (coe d_get'45'a5_246 (coe v0))
                  (coe d_get'45'a6_248 (coe v0)) (coe d_get'45'a7_250 (coe v0))
                  (coe d_get'45's1_252 (coe v0)) (coe d_get'45's2_254 (coe v0))
                  (coe d_get'45's3_256 (coe v0)) (coe d_get'45's4_258 (coe v0))
                  (coe v2) (coe d_get'45't1_262 (coe v0))
                  (coe d_get'45't2_264 (coe v0)) (coe d_get'45't3_266 (coe v0))
                  (coe d_get'45't4_268 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_270 (coe d_get'45'ra_230 (coe v0))
                  (coe d_get'45'sp_232 (coe v0)) (coe d_get'45'fp_234 (coe v0))
                  (coe d_get'45'a0_236 (coe v0)) (coe d_get'45'a1_238 (coe v0))
                  (coe d_get'45'a2_240 (coe v0)) (coe d_get'45'a3_242 (coe v0))
                  (coe d_get'45'a4_244 (coe v0)) (coe d_get'45'a5_246 (coe v0))
                  (coe d_get'45'a6_248 (coe v0)) (coe d_get'45'a7_250 (coe v0))
                  (coe d_get'45's1_252 (coe v0)) (coe d_get'45's2_254 (coe v0))
                  (coe d_get'45's3_256 (coe v0)) (coe d_get'45's4_258 (coe v0))
                  (coe d_get'45't0_260 (coe v0)) (coe v2)
                  (coe d_get'45't2_264 (coe v0)) (coe d_get'45't3_266 (coe v0))
                  (coe d_get'45't4_268 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t2_46
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_270 (coe d_get'45'ra_230 (coe v0))
                  (coe d_get'45'sp_232 (coe v0)) (coe d_get'45'fp_234 (coe v0))
                  (coe d_get'45'a0_236 (coe v0)) (coe d_get'45'a1_238 (coe v0))
                  (coe d_get'45'a2_240 (coe v0)) (coe d_get'45'a3_242 (coe v0))
                  (coe d_get'45'a4_244 (coe v0)) (coe d_get'45'a5_246 (coe v0))
                  (coe d_get'45'a6_248 (coe v0)) (coe d_get'45'a7_250 (coe v0))
                  (coe d_get'45's1_252 (coe v0)) (coe d_get'45's2_254 (coe v0))
                  (coe d_get'45's3_256 (coe v0)) (coe d_get'45's4_258 (coe v0))
                  (coe d_get'45't0_260 (coe v0)) (coe d_get'45't1_262 (coe v0))
                  (coe v2) (coe d_get'45't3_266 (coe v0))
                  (coe d_get'45't4_268 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t3_48
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_270 (coe d_get'45'ra_230 (coe v0))
                  (coe d_get'45'sp_232 (coe v0)) (coe d_get'45'fp_234 (coe v0))
                  (coe d_get'45'a0_236 (coe v0)) (coe d_get'45'a1_238 (coe v0))
                  (coe d_get'45'a2_240 (coe v0)) (coe d_get'45'a3_242 (coe v0))
                  (coe d_get'45'a4_244 (coe v0)) (coe d_get'45'a5_246 (coe v0))
                  (coe d_get'45'a6_248 (coe v0)) (coe d_get'45'a7_250 (coe v0))
                  (coe d_get'45's1_252 (coe v0)) (coe d_get'45's2_254 (coe v0))
                  (coe d_get'45's3_256 (coe v0)) (coe d_get'45's4_258 (coe v0))
                  (coe d_get'45't0_260 (coe v0)) (coe d_get'45't1_262 (coe v0))
                  (coe d_get'45't2_264 (coe v0)) (coe v2)
                  (coe d_get'45't4_268 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t4_50
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_270 (coe d_get'45'ra_230 (coe v0))
                  (coe d_get'45'sp_232 (coe v0)) (coe d_get'45'fp_234 (coe v0))
                  (coe d_get'45'a0_236 (coe v0)) (coe d_get'45'a1_238 (coe v0))
                  (coe d_get'45'a2_240 (coe v0)) (coe d_get'45'a3_242 (coe v0))
                  (coe d_get'45'a4_244 (coe v0)) (coe d_get'45'a5_246 (coe v0))
                  (coe d_get'45'a6_248 (coe v0)) (coe d_get'45'a7_250 (coe v0))
                  (coe d_get'45's1_252 (coe v0)) (coe d_get'45's2_254 (coe v0))
                  (coe d_get'45's3_256 (coe v0)) (coe d_get'45's4_258 (coe v0))
                  (coe d_get'45't0_260 (coe v0)) (coe d_get'45't1_262 (coe v0))
                  (coe d_get'45't2_264 (coe v0)) (coe d_get'45't3_266 (coe v0))
                  (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.Addr
d_Addr_402 :: ()
d_Addr_402 = erased
-- Once.CCC.Target.RiscV64.Semantics.Memory
d_Memory_404 :: ()
d_Memory_404 = erased
-- Once.CCC.Target.RiscV64.Semantics.readMem
d_readMem_406 ::
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
d_readMem_406 v0 v1 = coe v0 v1
-- Once.CCC.Target.RiscV64.Semantics.writeMem
d_writeMem_412 ::
  (Integer -> Maybe Integer) ->
  Integer -> Integer -> Integer -> Maybe Integer
d_writeMem_412 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v3) (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
      (coe v0 v3)
-- Once.CCC.Target.RiscV64.Semantics.State
d_State_422 = ()
data T_State_422
  = C_mkstate_440 T_RegFile_188 (Integer -> Maybe Integer) Integer
                  Bool
-- Once.CCC.Target.RiscV64.Semantics.State.regs
d_regs_432 :: T_State_422 -> T_RegFile_188
d_regs_432 v0
  = case coe v0 of
      C_mkstate_440 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.State.memory
d_memory_434 :: T_State_422 -> Integer -> Maybe Integer
d_memory_434 v0
  = case coe v0 of
      C_mkstate_440 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.State.pc
d_pc_436 :: T_State_422 -> Integer
d_pc_436 v0
  = case coe v0 of
      C_mkstate_440 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.State.halted
d_halted_438 :: T_State_422 -> Bool
d_halted_438 v0
  = case coe v0 of
      C_mkstate_440 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.emptyRegFile
d_emptyRegFile_442 :: T_RegFile_188
d_emptyRegFile_442
  = coe
      C_mkregfile_270 (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.emptyMemory
d_emptyMemory_444 :: Integer -> Maybe Integer
d_emptyMemory_444 ~v0 = du_emptyMemory_444
du_emptyMemory_444 :: Maybe Integer
du_emptyMemory_444
  = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.CCC.Target.RiscV64.Semantics.stack-top
d_stack'45'top_448
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Target.RiscV64.Semantics.stack-top"
-- Once.CCC.Target.RiscV64.Semantics.initStateAt
d_initStateAt_450 :: Integer -> T_State_422
d_initStateAt_450 v0
  = coe
      C_mkstate_440
      (coe
         d_writeReg_316 d_emptyRegFile_442
         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
         d_stack'45'top_448)
      (\ v1 -> coe du_emptyMemory_444) (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.CCC.Target.RiscV64.Semantics.initState
d_initState_454 :: T_State_422
d_initState_454 = coe d_initStateAt_450 (coe (0 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.effectiveAddr
d_effectiveAddr_456 ::
  T_RegFile_188 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  Integer -> Integer
d_effectiveAddr_456 v0 v1 v2
  = coe addInt (coe d_readReg_272 (coe v0) (coe v1)) (coe v2)
-- Once.CCC.Target.RiscV64.Semantics.effectiveAddrSigned
d_effectiveAddrSigned_464 ::
  T_RegFile_188 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  Integer -> Integer
d_effectiveAddrSigned_464 v0 v1 v2
  = let v3 = d_isNegative_186 (coe v2) in
    coe
      (if coe v3
         then coe
                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                (d_readReg_272 (coe v0) (coe v1))
                (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v2))
         else coe
                addInt (coe d_readReg_272 (coe v0) (coe v1))
                (coe d_offsetToℕ_180 (coe v2)))
-- Once.CCC.Target.RiscV64.Semantics.pcPlusOffset
d_pcPlusOffset_488 :: Integer -> Integer -> Integer
d_pcPlusOffset_488 v0 v1
  = let v2 = d_isNegative_186 (coe v1) in
    coe
      (if coe v2
         then coe
                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0
                (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1))
         else coe addInt (coe d_offsetToℕ_180 (coe v1)) (coe v0))
-- Once.CCC.Target.RiscV64.Semantics.fetch
d_fetch_506 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10
d_fetch_506 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe d_fetch_506 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.find-label-go
d_find'45'label'45'go_514 ::
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  Integer -> Maybe Integer
d_find'45'label'45'go_514 v0 v1 v2
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v3 v4
        -> let v5
                 = d_find'45'label'45'go_514
                     (coe v0) (coe v4) (coe addInt (coe (1 :: Integer)) (coe v2)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_54 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe
                          MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7480'__252 (coe v6)
                          (coe v0))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
                       (coe
                          d_find'45'label'45'go_514 (coe v0) (coe v4)
                          (coe addInt (coe (1 :: Integer)) (coe v2)))
                _ -> coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.find-label
d_find'45'label_532 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 -> Maybe Integer
d_find'45'label_532 v0 v1
  = coe
      d_find'45'label'45'go_514 (coe v1) (coe v0) (coe (0 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.jump-to
d_jump'45'to_538 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  T_State_422 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 -> Maybe T_State_422
d_jump'45'to_538 v0 v1 v2
  = let v3
          = d_find'45'label'45'go_514
              (coe v2) (coe v0) (coe (0 :: Integer)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   C_mkstate_440 (coe d_regs_432 (coe v1)) (coe d_memory_434 (coe v1))
                   (coe v4) (coe d_halted_438 (coe v1)))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   C_mkstate_440 (coe d_regs_432 (coe v1)) (coe d_memory_434 (coe v1))
                   (coe d_pc_436 (coe v1))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Target.RiscV64.Semantics.execInstr
d_execInstr_564 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  T_State_422 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10 ->
  Maybe T_State_422
d_execInstr_564 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12 v3 v4 v5
        -> let v6
                 = coe
                     d_memory_434 v1
                     (d_effectiveAddr_456
                        (coe d_regs_432 (coe v1)) (coe v4) (coe v5)) in
           coe
             (case coe v6 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_440 (coe d_writeReg_316 (d_regs_432 (coe v1)) v3 v7)
                          (coe d_memory_434 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_436 (coe v1)))
                          (coe d_halted_438 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_440 (coe d_regs_432 (coe v1))
                (coe
                   d_writeMem_412 (coe d_memory_434 (coe v1))
                   (coe
                      d_effectiveAddr_456 (coe d_regs_432 (coe v1)) (coe v4) (coe v5))
                   (coe d_readReg_272 (coe d_regs_432 (coe v1)) (coe v3)))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_436 (coe v1)))
                (coe d_halted_438 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_add_16 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_440
                (coe
                   d_writeReg_316 (d_regs_432 (coe v1)) v3
                   (MAlonzo.Code.Once.Spec.Word.d__'8853'__28
                      (coe (64 :: Integer))
                      (coe d_readReg_272 (coe d_regs_432 (coe v1)) (coe v4))
                      (coe d_readReg_272 (coe d_regs_432 (coe v1)) (coe v5))))
                (coe d_memory_434 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_436 (coe v1)))
                (coe d_halted_438 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sub_18 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_440
                (coe
                   d_writeReg_316 (d_regs_432 (coe v1)) v3
                   (MAlonzo.Code.Once.Spec.Word.d__'8854'__34
                      (coe (64 :: Integer))
                      (coe d_readReg_272 (coe d_regs_432 (coe v1)) (coe v4))
                      (coe d_readReg_272 (coe d_regs_432 (coe v1)) (coe v5))))
                (coe d_memory_434 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_436 (coe v1)))
                (coe d_halted_438 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sltu_20 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_440
                (coe
                   d_writeReg_316 (d_regs_432 (coe v1)) v3
                   (coe
                      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                      (coe
                         ltInt (coe d_readReg_272 (coe d_regs_432 (coe v1)) (coe v4))
                         (coe d_readReg_272 (coe d_regs_432 (coe v1)) (coe v5)))
                      (coe (1 :: Integer)) (coe (0 :: Integer))))
                (coe d_memory_434 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_436 (coe v1)))
                (coe d_halted_438 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_22 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_440
                (coe
                   d_writeReg_316 (d_regs_432 (coe v1)) v3
                   (MAlonzo.Code.Once.Spec.Word.d__'8853'__28
                      (coe (64 :: Integer))
                      (coe d_readReg_272 (coe d_regs_432 (coe v1)) (coe v4))
                      (coe
                         MAlonzo.Code.Once.Spec.Word.d_fromℤ_22 (coe (64 :: Integer))
                         (coe v5))))
                (coe d_memory_434 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_436 (coe v1)))
                (coe d_halted_438 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_24 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_440
                (coe
                   d_writeReg_316 (d_regs_432 (coe v1)) v3
                   (MAlonzo.Code.Once.Spec.Word.d_fromℤ_22
                      (coe (64 :: Integer)) (coe v4)))
                (coe d_memory_434 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_436 (coe v1)))
                (coe d_halted_438 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_auipc_26 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_440
                (coe
                   d_writeReg_316 (d_regs_432 (coe v1)) v3
                   (addInt
                      (coe d_pc_436 (coe v1))
                      (coe mulInt (coe v4) (coe (4096 :: Integer)))))
                (coe d_memory_434 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_436 (coe v1)))
                (coe d_halted_438 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_lla_28 v3 v4
        -> let v5
                 = d_find'45'label_532
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
                          C_mkstate_440 (coe d_writeReg_316 (d_regs_432 (coe v1)) v3 v6)
                          (coe d_memory_434 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_436 (coe v1)))
                          (coe d_halted_438 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_440 (coe d_regs_432 (coe v1)) (coe d_memory_434 (coe v1))
                          (coe d_pc_436 (coe v1))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_lla'45'sym_30 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_440
                (coe d_writeReg_316 (d_regs_432 (coe v1)) v3 (0 :: Integer))
                (coe d_memory_434 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_436 (coe v1)))
                (coe d_halted_438 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_440
                (coe
                   d_writeReg_316 (d_regs_432 (coe v1)) v3
                   (d_readReg_272 (coe d_regs_432 (coe v1)) (coe v4)))
                (coe d_memory_434 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_436 (coe v1)))
                (coe d_halted_438 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_beq_34 v3 v4 v5
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                eqInt (coe d_readReg_272 (coe d_regs_432 (coe v1)) (coe v3))
                (coe d_readReg_272 (coe d_regs_432 (coe v1)) (coe v4)))
             (coe d_jump'45'to_538 (coe v0) (coe v1) (coe v5))
             (coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   C_mkstate_440 (coe d_regs_432 (coe v1)) (coe d_memory_434 (coe v1))
                   (coe addInt (coe (1 :: Integer)) (coe d_pc_436 (coe v1)))
                   (coe d_halted_438 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_bne_36 v3 v4 v5
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                eqInt (coe d_readReg_272 (coe d_regs_432 (coe v1)) (coe v3))
                (coe d_readReg_272 (coe d_regs_432 (coe v1)) (coe v4)))
             (coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   C_mkstate_440 (coe d_regs_432 (coe v1)) (coe d_memory_434 (coe v1))
                   (coe addInt (coe (1 :: Integer)) (coe d_pc_436 (coe v1)))
                   (coe d_halted_438 (coe v1))))
             (coe d_jump'45'to_538 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_jal_38 v3 v4
        -> coe
             d_jump'45'to_538 (coe v0)
             (coe
                C_mkstate_440
                (coe
                   d_writeReg_316 (d_regs_432 (coe v1)) v3
                   (addInt (coe (1 :: Integer)) (coe d_pc_436 (coe v1))))
                (coe d_memory_434 (coe v1)) (coe d_pc_436 (coe v1))
                (coe d_halted_438 (coe v1)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_jalr_40 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_440
                (coe
                   d_writeReg_316 (d_regs_432 (coe v1)) v3
                   (addInt (coe (1 :: Integer)) (coe d_pc_436 (coe v1))))
                (coe d_memory_434 (coe v1))
                (coe
                   d_effectiveAddr_456 (coe d_regs_432 (coe v1)) (coe v4) (coe v5))
                (coe d_halted_438 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_j_42 v3
        -> coe d_jump'45'to_538 (coe v0) (coe v1) (coe v3)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ret_44
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_440 (coe d_regs_432 (coe v1)) (coe d_memory_434 (coe v1))
                (coe
                   d_readReg_272 (coe d_regs_432 (coe v1))
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_ra_12))
                (coe d_halted_438 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call_46 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_440
                (coe
                   d_writeReg_316 (d_regs_432 (coe v1))
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_ra_12)
                   (addInt (coe (1 :: Integer)) (coe d_pc_436 (coe v1))))
                (coe d_memory_434 (coe v1))
                (coe addInt (coe d_pc_436 (coe v1)) (coe v3))
                (coe d_halted_438 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call'45'sym_48 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_440 (coe d_regs_432 (coe v1)) (coe d_memory_434 (coe v1))
                (coe d_pc_436 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_nop_50
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_440 (coe d_regs_432 (coe v1)) (coe d_memory_434 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_436 (coe v1)))
                (coe d_halted_438 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_unimp_52
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_440 (coe d_regs_432 (coe v1)) (coe d_memory_434 (coe v1))
                (coe d_pc_436 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_54 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_440 (coe d_regs_432 (coe v1)) (coe d_memory_434 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_436 (coe v1)))
                (coe d_halted_438 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.step-not-halted
d_step'45'not'45'halted_806 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  T_State_422 -> Maybe T_State_422
d_step'45'not'45'halted_806 v0 v1
  = let v2 = d_fetch_506 (coe v0) (coe d_pc_436 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe d_execInstr_564 (coe v0) (coe v1) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   C_mkstate_440 (coe d_regs_432 (coe v1)) (coe d_memory_434 (coe v1))
                   (coe d_pc_436 (coe v1))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Target.RiscV64.Semantics.step
d_step_816 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  T_State_422 -> Maybe T_State_422
d_step_816 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_halted_438 (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1))
      (coe d_step'45'not'45'halted_806 (coe v0) (coe v1))
-- Once.CCC.Target.RiscV64.Semantics.exec
d_exec_822 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  T_State_422 -> Maybe T_State_422
d_exec_822 v0 v1 v2
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe d_halted_438 (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
                (coe
                   d_exec'45'cont_824 (coe v3) (coe v1)
                   (coe d_step'45'not'45'halted_806 (coe v1) (coe v2))))
-- Once.CCC.Target.RiscV64.Semantics.exec-cont
d_exec'45'cont_824 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  Maybe T_State_422 -> Maybe T_State_422
d_exec'45'cont_824 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_halted_438 (coe v3)) (coe v2)
             (coe d_exec_822 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.exec-until-pc
d_exec'45'until'45'pc_844 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  T_State_422 -> Maybe T_State_422
d_exec'45'until'45'pc_844 v0 v1 v2 v3
  = case coe v1 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v5 = d_halted_438 (coe v3) in
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
                                        (coe d_pc_436 (coe v3)))
                                   (coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                      (coe eqInt (coe d_pc_436 (coe v3)) (coe v0))) in
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
                                                          d_step'45'not'45'halted_806 (coe v2)
                                                          (coe v3)) in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> coe
                                                         d_exec'45'until'45'pc_844 (coe v0) (coe v4)
                                                         (coe v2) (coe v10)
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> coe v9
                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Target.RiscV64.Semantics.defaultFuel
d_defaultFuel_922 :: Integer
d_defaultFuel_922 = coe (10000 :: Integer)
-- Once.CCC.Target.RiscV64.Semantics.run
d_run_924 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  T_State_422 -> Maybe T_State_422
d_run_924 = coe d_exec_822 (coe d_defaultFuel_922)
