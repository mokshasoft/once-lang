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

module MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics where

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
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg
import qualified MAlonzo.Code.Once.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Target.X86-64.Semantics.W._%ˢ_
d__'37''738'__12 :: Integer -> Integer -> Integer
d__'37''738'__12
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__126 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W._/ˢ_
d__'47''738'__14 :: Integer -> Integer -> Integer
d__'47''738'__14
  = coe
      MAlonzo.Code.Once.Word.d__'47''738'__120 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W._<ˢ_
d__'60''738'__16 :: Integer -> Integer -> Bool
d__'60''738'__16
  = coe MAlonzo.Code.Once.Word.d__'60''738'__80 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W._≡ʷ_
d__'8801''695'__18 :: Integer -> Integer -> Bool
d__'8801''695'__18 = coe MAlonzo.Code.Once.Word.du__'8801''695'__86
-- Once.CCC.Target.X86-64.Semantics.W._⊕_
d__'8853'__20 :: Integer -> Integer -> Integer
d__'8853'__20
  = coe MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W._⊖_
d__'8854'__22 :: Integer -> Integer -> Integer
d__'8854'__22
  = coe MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W._⊗_
d__'8855'__24 :: Integer -> Integer -> Integer
d__'8855'__24
  = coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.%ˢ-else
d_'37''738''45'else_26 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_26 = erased
-- Once.CCC.Target.X86-64.Semantics.W.%ˢ-in-range
d_'37''738''45'in'45'range_28 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_28 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_604
      (coe (64 :: Integer)) v2 v3 v4
-- Once.CCC.Target.X86-64.Semantics.W.%ˢ-mid
d_'37''738''45'mid_30 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_30 = erased
-- Once.CCC.Target.X86-64.Semantics.W.%ˢ-negOne
d_'37''738''45'negOne_32 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_32 = erased
-- Once.CCC.Target.X86-64.Semantics.W.%ˢ-zero
d_'37''738''45'zero_34 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_34 = erased
-- Once.CCC.Target.X86-64.Semantics.W./ˢ-else
d_'47''738''45'else_36 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_36 = erased
-- Once.CCC.Target.X86-64.Semantics.W./ˢ-in-range
d_'47''738''45'in'45'range_38 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_38 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_570
      (coe (64 :: Integer)) v2 v3
-- Once.CCC.Target.X86-64.Semantics.W./ˢ-mid
d_'47''738''45'mid_40 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_40 = erased
-- Once.CCC.Target.X86-64.Semantics.W./ˢ-negOne
d_'47''738''45'negOne_42 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_42 = erased
-- Once.CCC.Target.X86-64.Semantics.W./ˢ-pow2
d_'47''738''45'pow2_44 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_44 = erased
-- Once.CCC.Target.X86-64.Semantics.W./ˢ-zero
d_'47''738''45'zero_46 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_46 = erased
-- Once.CCC.Target.X86-64.Semantics.W.0<half
d_0'60'half_48 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_48 = coe MAlonzo.Code.Once.Word.du_0'60'half_168
-- Once.CCC.Target.X86-64.Semantics.W.0<modulus
d_0'60'modulus_50 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_50 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_166
-- Once.CCC.Target.X86-64.Semantics.W.0<negOne
d_0'60'negOne_52 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_52 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_426 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.1<modulus
d_1'60'modulus_54 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_54
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_796 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.2*n≡n+n
d_2'42'n'8801'n'43'n_56 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_56 = erased
-- Once.CCC.Target.X86-64.Semantics.W.2≤modulus
d_2'8804'modulus_58 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_58 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_422 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.<⇒<ᵇtrue
d_'60''8658''60''7495'true_60 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8658''60''7495'true_60 = erased
-- Once.CCC.Target.X86-64.Semantics.W.InRange
d_InRange_62 :: Integer -> ()
d_InRange_62 = erased
-- Once.CCC.Target.X86-64.Semantics.W.Word
d_Word_64 :: ()
d_Word_64 = erased
-- Once.CCC.Target.X86-64.Semantics.W.fromℤ
d_fromℤ_66 :: Integer -> Integer
d_fromℤ_66
  = coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.fromℤ-0
d_fromℤ'45'0_68 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_68 = erased
-- Once.CCC.Target.X86-64.Semantics.W.fromℤ-in-range
d_fromℤ'45'in'45'range_70 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_70
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_174
      (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_72 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_72 = erased
-- Once.CCC.Target.X86-64.Semantics.W.fromℤ-neg1
d_fromℤ'45'neg1_74 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_74 = erased
-- Once.CCC.Target.X86-64.Semantics.W.half
d_half_76 :: Integer
d_half_76
  = coe MAlonzo.Code.Once.Word.d_half_48 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.half<modulus
d_half'60'modulus_78 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_78 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_430 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.half≡2^b
d_half'8801'2'94'b_80 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_80 = erased
-- Once.CCC.Target.X86-64.Semantics.W.half≤negOne
d_half'8804'negOne_82 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_82 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_450
      (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.inRange?
d_inRange'63'_84 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_84
  = coe MAlonzo.Code.Once.Word.d_inRange'63'_62 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.intMin
d_intMin_86 :: Integer
d_intMin_86
  = coe MAlonzo.Code.Once.Word.d_intMin_54 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.lit-hi
d_lit'45'hi_88 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'hi_88 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Word.du_lit'45'hi_654 v3
-- Once.CCC.Target.X86-64.Semantics.W.lit-lo
d_lit'45'lo_90 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'lo_90 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_lit'45'lo_666 (coe (64 :: Integer)) v2 v3
-- Once.CCC.Target.X86-64.Semantics.W.modulus
d_modulus_92 :: Integer
d_modulus_92
  = coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_94 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_94 = erased
-- Once.CCC.Target.X86-64.Semantics.W.modulus≢0
d_modulus'8802'0_96 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_96
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.mod∸half≡half
d_mod'8760'half'8801'half_98 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_98 = erased
-- Once.CCC.Target.X86-64.Semantics.W.mod≡half+half
d_mod'8801'half'43'half_100 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_100 = erased
-- Once.CCC.Target.X86-64.Semantics.W.negOne
d_negOne_102 :: Integer
d_negOne_102
  = coe MAlonzo.Code.Once.Word.d_negOne_78 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.negOne<modulus
d_negOne'60'modulus_104 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_104 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_438
      (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.negOne≢0
d_negOne'8802'0_106 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_106 = erased
-- Once.CCC.Target.X86-64.Semantics.W.norm
d_norm_108 :: Integer -> Integer
d_norm_108
  = coe MAlonzo.Code.Once.Word.d_norm_16 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.norm-0
d_norm'45'0_110 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_110 = erased
-- Once.CCC.Target.X86-64.Semantics.W.norm-id
d_norm'45'id_112 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_112 = erased
-- Once.CCC.Target.X86-64.Semantics.W.sbb-pos
d_sbb'45'pos_114 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sbb'45'pos_114 = erased
-- Once.CCC.Target.X86-64.Semantics.W.sbb-zero
d_sbb'45'zero_116 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sbb'45'zero_116 = erased
-- Once.CCC.Target.X86-64.Semantics.W.sdiv2ᵏ
d_sdiv2'7503'_118 :: Integer -> Integer -> Integer
d_sdiv2'7503'_118
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_138 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.shlᵂ
d_shl'7490'_120 :: Integer -> Integer -> Integer
d_shl'7490'_120
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_132 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.sucNegOne≡mod
d_sucNegOne'8801'mod_122 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_122 = erased
-- Once.CCC.Target.X86-64.Semantics.W.tdiv-neg1
d_tdiv'45'neg1_124 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_124 = erased
-- Once.CCC.Target.X86-64.Semantics.W.tmod-neg1
d_tmod'45'neg1_126 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_126 = erased
-- Once.CCC.Target.X86-64.Semantics.W.toWord
d_toWord_128 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_128 v0 v1
  = coe MAlonzo.Code.Once.Word.du_toWord_68 (coe (64 :: Integer)) v0
-- Once.CCC.Target.X86-64.Semantics.W.toWord≡fromℤ
d_toWord'8801'fromℤ_130 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'8801'fromℤ_130 = erased
-- Once.CCC.Target.X86-64.Semantics.W.toℤ
d_toℤ_132 :: Integer -> Integer
d_toℤ_132
  = coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.toℤ-negOne
d_toℤ'45'negOne_134 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_134 = erased
-- Once.CCC.Target.X86-64.Semantics.W.toℤ∘fromℤ
d_toℤ'8728'fromℤ_136 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'8728'fromℤ_136 = erased
-- Once.CCC.Target.X86-64.Semantics.W.unplus
d_unplus_138 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_unplus_138 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Word.du_unplus_648 v4
-- Once.CCC.Target.X86-64.Semantics.W.≡ᵇ-refl
d_'8801''7495''45'refl_140 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_140 = erased
-- Once.CCC.Target.X86-64.Semantics.W.≡ᵇ0-false
d_'8801''7495'0'45'false_142 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_142 = erased
-- Once.CCC.Target.X86-64.Semantics.W.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_144 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_144 = erased
-- Once.CCC.Target.X86-64.Semantics.W.⊕-neg
d_'8853''45'neg_146 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_146 = erased
-- Once.CCC.Target.X86-64.Semantics.W.⊕-neg-suc
d_'8853''45'neg'45'suc_148 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_148 = erased
-- Once.CCC.Target.X86-64.Semantics.W.⊕-normʳ
d_'8853''45'norm'691'_150 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_150 = erased
-- Once.CCC.Target.X86-64.Semantics.W.⊕≡+
d_'8853''8801''43'_152 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_152 = erased
-- Once.CCC.Target.X86-64.Semantics.W.⊖-normʳ
d_'8854''45'norm'691'_154 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_154 = erased
-- Once.CCC.Target.X86-64.Semantics.W.⊖-self
d_'8854''45'self_156 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'self_156 = erased
-- Once.CCC.Target.X86-64.Semantics.W.⊖≡∸
d_'8854''8801''8760'_158 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_158 = erased
-- Once.CCC.Target.X86-64.Semantics.W.⊗-pow2
d_'8855''45'pow2_160 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_160 = erased
-- Once.CCC.Target.X86-64.Semantics.W.⊝_
d_'8861'__162 :: Integer -> Integer
d_'8861'__162
  = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.⊝-fromℤ
d_'8861''45'fromℤ_164 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'fromℤ_164 = erased
-- Once.CCC.Target.X86-64.Semantics.W.⊝-intMin
d_'8861''45'intMin_166 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_166 = erased
-- Once.CCC.Target.X86-64.Semantics.W.⊝-invol-norm
d_'8861''45'invol'45'norm_168 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'invol'45'norm_168 = erased
-- Once.CCC.Target.X86-64.Semantics.Word
d_Word_170 :: ()
d_Word_170 = erased
-- Once.CCC.Target.X86-64.Semantics.RegFile
d_RegFile_172 = ()
data T_RegFile_172
  = C_mkregfile_238 Integer Integer Integer Integer Integer Integer
                    Integer Integer Integer Integer Integer Integer Integer Integer
                    Integer Integer
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rax
d_get'45'rax_206 :: T_RegFile_172 -> Integer
d_get'45'rax_206 v0
  = case coe v0 of
      C_mkregfile_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rbx
d_get'45'rbx_208 :: T_RegFile_172 -> Integer
d_get'45'rbx_208 v0
  = case coe v0 of
      C_mkregfile_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rcx
d_get'45'rcx_210 :: T_RegFile_172 -> Integer
d_get'45'rcx_210 v0
  = case coe v0 of
      C_mkregfile_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rdx
d_get'45'rdx_212 :: T_RegFile_172 -> Integer
d_get'45'rdx_212 v0
  = case coe v0 of
      C_mkregfile_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rsi
d_get'45'rsi_214 :: T_RegFile_172 -> Integer
d_get'45'rsi_214 v0
  = case coe v0 of
      C_mkregfile_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rdi
d_get'45'rdi_216 :: T_RegFile_172 -> Integer
d_get'45'rdi_216 v0
  = case coe v0 of
      C_mkregfile_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rbp
d_get'45'rbp_218 :: T_RegFile_172 -> Integer
d_get'45'rbp_218 v0
  = case coe v0 of
      C_mkregfile_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rsp
d_get'45'rsp_220 :: T_RegFile_172 -> Integer
d_get'45'rsp_220 v0
  = case coe v0 of
      C_mkregfile_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r8
d_get'45'r8_222 :: T_RegFile_172 -> Integer
d_get'45'r8_222 v0
  = case coe v0 of
      C_mkregfile_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r9
d_get'45'r9_224 :: T_RegFile_172 -> Integer
d_get'45'r9_224 v0
  = case coe v0 of
      C_mkregfile_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r10
d_get'45'r10_226 :: T_RegFile_172 -> Integer
d_get'45'r10_226 v0
  = case coe v0 of
      C_mkregfile_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r11
d_get'45'r11_228 :: T_RegFile_172 -> Integer
d_get'45'r11_228 v0
  = case coe v0 of
      C_mkregfile_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r12
d_get'45'r12_230 :: T_RegFile_172 -> Integer
d_get'45'r12_230 v0
  = case coe v0 of
      C_mkregfile_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r13
d_get'45'r13_232 :: T_RegFile_172 -> Integer
d_get'45'r13_232 v0
  = case coe v0 of
      C_mkregfile_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r14
d_get'45'r14_234 :: T_RegFile_172 -> Integer
d_get'45'r14_234 v0
  = case coe v0 of
      C_mkregfile_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r15
d_get'45'r15_236 :: T_RegFile_172 -> Integer
d_get'45'r15_236 v0
  = case coe v0 of
      C_mkregfile_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.readReg
d_readReg_240 ::
  T_RegFile_172 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer
d_readReg_240 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10
        -> coe d_get'45'rax_206 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12
        -> coe d_get'45'rbx_208 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rcx_14
        -> coe d_get'45'rcx_210 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdx_16
        -> coe d_get'45'rdx_212 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsi_18
        -> coe d_get'45'rsi_214 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20
        -> coe d_get'45'rdi_216 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbp_22
        -> coe d_get'45'rbp_218 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24
        -> coe d_get'45'rsp_220 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r8_26
        -> coe d_get'45'r8_222 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r9_28
        -> coe d_get'45'r9_224 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r10_30
        -> coe d_get'45'r10_226 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r11_32
        -> coe d_get'45'r11_228 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r12_34
        -> coe d_get'45'r12_230 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r13_36
        -> coe d_get'45'r13_232 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r14_38
        -> coe d_get'45'r14_234 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r15_40
        -> coe d_get'45'r15_236 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.writeReg
d_writeReg_274 ::
  T_RegFile_172 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer -> T_RegFile_172
d_writeReg_274 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_238 (coe v2) (coe d_get'45'rbx_208 (coe v0))
                  (coe d_get'45'rcx_210 (coe v0)) (coe d_get'45'rdx_212 (coe v0))
                  (coe d_get'45'rsi_214 (coe v0)) (coe d_get'45'rdi_216 (coe v0))
                  (coe d_get'45'rbp_218 (coe v0)) (coe d_get'45'rsp_220 (coe v0))
                  (coe d_get'45'r8_222 (coe v0)) (coe d_get'45'r9_224 (coe v0))
                  (coe d_get'45'r10_226 (coe v0)) (coe d_get'45'r11_228 (coe v0))
                  (coe d_get'45'r12_230 (coe v0)) (coe d_get'45'r13_232 (coe v0))
                  (coe d_get'45'r14_234 (coe v0)) (coe d_get'45'r15_236 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_238 (coe d_get'45'rax_206 (coe v0)) (coe v2)
                  (coe d_get'45'rcx_210 (coe v0)) (coe d_get'45'rdx_212 (coe v0))
                  (coe d_get'45'rsi_214 (coe v0)) (coe d_get'45'rdi_216 (coe v0))
                  (coe d_get'45'rbp_218 (coe v0)) (coe d_get'45'rsp_220 (coe v0))
                  (coe d_get'45'r8_222 (coe v0)) (coe d_get'45'r9_224 (coe v0))
                  (coe d_get'45'r10_226 (coe v0)) (coe d_get'45'r11_228 (coe v0))
                  (coe d_get'45'r12_230 (coe v0)) (coe d_get'45'r13_232 (coe v0))
                  (coe d_get'45'r14_234 (coe v0)) (coe d_get'45'r15_236 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rcx_14
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_238 (coe d_get'45'rax_206 (coe v0))
                  (coe d_get'45'rbx_208 (coe v0)) (coe v2)
                  (coe d_get'45'rdx_212 (coe v0)) (coe d_get'45'rsi_214 (coe v0))
                  (coe d_get'45'rdi_216 (coe v0)) (coe d_get'45'rbp_218 (coe v0))
                  (coe d_get'45'rsp_220 (coe v0)) (coe d_get'45'r8_222 (coe v0))
                  (coe d_get'45'r9_224 (coe v0)) (coe d_get'45'r10_226 (coe v0))
                  (coe d_get'45'r11_228 (coe v0)) (coe d_get'45'r12_230 (coe v0))
                  (coe d_get'45'r13_232 (coe v0)) (coe d_get'45'r14_234 (coe v0))
                  (coe d_get'45'r15_236 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdx_16
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_238 (coe d_get'45'rax_206 (coe v0))
                  (coe d_get'45'rbx_208 (coe v0)) (coe d_get'45'rcx_210 (coe v0))
                  (coe v2) (coe d_get'45'rsi_214 (coe v0))
                  (coe d_get'45'rdi_216 (coe v0)) (coe d_get'45'rbp_218 (coe v0))
                  (coe d_get'45'rsp_220 (coe v0)) (coe d_get'45'r8_222 (coe v0))
                  (coe d_get'45'r9_224 (coe v0)) (coe d_get'45'r10_226 (coe v0))
                  (coe d_get'45'r11_228 (coe v0)) (coe d_get'45'r12_230 (coe v0))
                  (coe d_get'45'r13_232 (coe v0)) (coe d_get'45'r14_234 (coe v0))
                  (coe d_get'45'r15_236 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsi_18
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_238 (coe d_get'45'rax_206 (coe v0))
                  (coe d_get'45'rbx_208 (coe v0)) (coe d_get'45'rcx_210 (coe v0))
                  (coe d_get'45'rdx_212 (coe v0)) (coe v2)
                  (coe d_get'45'rdi_216 (coe v0)) (coe d_get'45'rbp_218 (coe v0))
                  (coe d_get'45'rsp_220 (coe v0)) (coe d_get'45'r8_222 (coe v0))
                  (coe d_get'45'r9_224 (coe v0)) (coe d_get'45'r10_226 (coe v0))
                  (coe d_get'45'r11_228 (coe v0)) (coe d_get'45'r12_230 (coe v0))
                  (coe d_get'45'r13_232 (coe v0)) (coe d_get'45'r14_234 (coe v0))
                  (coe d_get'45'r15_236 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_238 (coe d_get'45'rax_206 (coe v0))
                  (coe d_get'45'rbx_208 (coe v0)) (coe d_get'45'rcx_210 (coe v0))
                  (coe d_get'45'rdx_212 (coe v0)) (coe d_get'45'rsi_214 (coe v0))
                  (coe v2) (coe d_get'45'rbp_218 (coe v0))
                  (coe d_get'45'rsp_220 (coe v0)) (coe d_get'45'r8_222 (coe v0))
                  (coe d_get'45'r9_224 (coe v0)) (coe d_get'45'r10_226 (coe v0))
                  (coe d_get'45'r11_228 (coe v0)) (coe d_get'45'r12_230 (coe v0))
                  (coe d_get'45'r13_232 (coe v0)) (coe d_get'45'r14_234 (coe v0))
                  (coe d_get'45'r15_236 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbp_22
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_238 (coe d_get'45'rax_206 (coe v0))
                  (coe d_get'45'rbx_208 (coe v0)) (coe d_get'45'rcx_210 (coe v0))
                  (coe d_get'45'rdx_212 (coe v0)) (coe d_get'45'rsi_214 (coe v0))
                  (coe d_get'45'rdi_216 (coe v0)) (coe v2)
                  (coe d_get'45'rsp_220 (coe v0)) (coe d_get'45'r8_222 (coe v0))
                  (coe d_get'45'r9_224 (coe v0)) (coe d_get'45'r10_226 (coe v0))
                  (coe d_get'45'r11_228 (coe v0)) (coe d_get'45'r12_230 (coe v0))
                  (coe d_get'45'r13_232 (coe v0)) (coe d_get'45'r14_234 (coe v0))
                  (coe d_get'45'r15_236 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_238 (coe d_get'45'rax_206 (coe v0))
                  (coe d_get'45'rbx_208 (coe v0)) (coe d_get'45'rcx_210 (coe v0))
                  (coe d_get'45'rdx_212 (coe v0)) (coe d_get'45'rsi_214 (coe v0))
                  (coe d_get'45'rdi_216 (coe v0)) (coe d_get'45'rbp_218 (coe v0))
                  (coe v2) (coe d_get'45'r8_222 (coe v0))
                  (coe d_get'45'r9_224 (coe v0)) (coe d_get'45'r10_226 (coe v0))
                  (coe d_get'45'r11_228 (coe v0)) (coe d_get'45'r12_230 (coe v0))
                  (coe d_get'45'r13_232 (coe v0)) (coe d_get'45'r14_234 (coe v0))
                  (coe d_get'45'r15_236 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r8_26
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_238 (coe d_get'45'rax_206 (coe v0))
                  (coe d_get'45'rbx_208 (coe v0)) (coe d_get'45'rcx_210 (coe v0))
                  (coe d_get'45'rdx_212 (coe v0)) (coe d_get'45'rsi_214 (coe v0))
                  (coe d_get'45'rdi_216 (coe v0)) (coe d_get'45'rbp_218 (coe v0))
                  (coe d_get'45'rsp_220 (coe v0)) (coe v2)
                  (coe d_get'45'r9_224 (coe v0)) (coe d_get'45'r10_226 (coe v0))
                  (coe d_get'45'r11_228 (coe v0)) (coe d_get'45'r12_230 (coe v0))
                  (coe d_get'45'r13_232 (coe v0)) (coe d_get'45'r14_234 (coe v0))
                  (coe d_get'45'r15_236 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r9_28
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_238 (coe d_get'45'rax_206 (coe v0))
                  (coe d_get'45'rbx_208 (coe v0)) (coe d_get'45'rcx_210 (coe v0))
                  (coe d_get'45'rdx_212 (coe v0)) (coe d_get'45'rsi_214 (coe v0))
                  (coe d_get'45'rdi_216 (coe v0)) (coe d_get'45'rbp_218 (coe v0))
                  (coe d_get'45'rsp_220 (coe v0)) (coe d_get'45'r8_222 (coe v0))
                  (coe v2) (coe d_get'45'r10_226 (coe v0))
                  (coe d_get'45'r11_228 (coe v0)) (coe d_get'45'r12_230 (coe v0))
                  (coe d_get'45'r13_232 (coe v0)) (coe d_get'45'r14_234 (coe v0))
                  (coe d_get'45'r15_236 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r10_30
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_238 (coe d_get'45'rax_206 (coe v0))
                  (coe d_get'45'rbx_208 (coe v0)) (coe d_get'45'rcx_210 (coe v0))
                  (coe d_get'45'rdx_212 (coe v0)) (coe d_get'45'rsi_214 (coe v0))
                  (coe d_get'45'rdi_216 (coe v0)) (coe d_get'45'rbp_218 (coe v0))
                  (coe d_get'45'rsp_220 (coe v0)) (coe d_get'45'r8_222 (coe v0))
                  (coe d_get'45'r9_224 (coe v0)) (coe v2)
                  (coe d_get'45'r11_228 (coe v0)) (coe d_get'45'r12_230 (coe v0))
                  (coe d_get'45'r13_232 (coe v0)) (coe d_get'45'r14_234 (coe v0))
                  (coe d_get'45'r15_236 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r11_32
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_238 (coe d_get'45'rax_206 (coe v0))
                  (coe d_get'45'rbx_208 (coe v0)) (coe d_get'45'rcx_210 (coe v0))
                  (coe d_get'45'rdx_212 (coe v0)) (coe d_get'45'rsi_214 (coe v0))
                  (coe d_get'45'rdi_216 (coe v0)) (coe d_get'45'rbp_218 (coe v0))
                  (coe d_get'45'rsp_220 (coe v0)) (coe d_get'45'r8_222 (coe v0))
                  (coe d_get'45'r9_224 (coe v0)) (coe d_get'45'r10_226 (coe v0))
                  (coe v2) (coe d_get'45'r12_230 (coe v0))
                  (coe d_get'45'r13_232 (coe v0)) (coe d_get'45'r14_234 (coe v0))
                  (coe d_get'45'r15_236 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r12_34
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_238 (coe d_get'45'rax_206 (coe v0))
                  (coe d_get'45'rbx_208 (coe v0)) (coe d_get'45'rcx_210 (coe v0))
                  (coe d_get'45'rdx_212 (coe v0)) (coe d_get'45'rsi_214 (coe v0))
                  (coe d_get'45'rdi_216 (coe v0)) (coe d_get'45'rbp_218 (coe v0))
                  (coe d_get'45'rsp_220 (coe v0)) (coe d_get'45'r8_222 (coe v0))
                  (coe d_get'45'r9_224 (coe v0)) (coe d_get'45'r10_226 (coe v0))
                  (coe d_get'45'r11_228 (coe v0)) (coe v2)
                  (coe d_get'45'r13_232 (coe v0)) (coe d_get'45'r14_234 (coe v0))
                  (coe d_get'45'r15_236 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r13_36
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_238 (coe d_get'45'rax_206 (coe v0))
                  (coe d_get'45'rbx_208 (coe v0)) (coe d_get'45'rcx_210 (coe v0))
                  (coe d_get'45'rdx_212 (coe v0)) (coe d_get'45'rsi_214 (coe v0))
                  (coe d_get'45'rdi_216 (coe v0)) (coe d_get'45'rbp_218 (coe v0))
                  (coe d_get'45'rsp_220 (coe v0)) (coe d_get'45'r8_222 (coe v0))
                  (coe d_get'45'r9_224 (coe v0)) (coe d_get'45'r10_226 (coe v0))
                  (coe d_get'45'r11_228 (coe v0)) (coe d_get'45'r12_230 (coe v0))
                  (coe v2) (coe d_get'45'r14_234 (coe v0))
                  (coe d_get'45'r15_236 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r14_38
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_238 (coe d_get'45'rax_206 (coe v0))
                  (coe d_get'45'rbx_208 (coe v0)) (coe d_get'45'rcx_210 (coe v0))
                  (coe d_get'45'rdx_212 (coe v0)) (coe d_get'45'rsi_214 (coe v0))
                  (coe d_get'45'rdi_216 (coe v0)) (coe d_get'45'rbp_218 (coe v0))
                  (coe d_get'45'rsp_220 (coe v0)) (coe d_get'45'r8_222 (coe v0))
                  (coe d_get'45'r9_224 (coe v0)) (coe d_get'45'r10_226 (coe v0))
                  (coe d_get'45'r11_228 (coe v0)) (coe d_get'45'r12_230 (coe v0))
                  (coe d_get'45'r13_232 (coe v0)) (coe v2)
                  (coe d_get'45'r15_236 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r15_40
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_238 (coe d_get'45'rax_206 (coe v0))
                  (coe d_get'45'rbx_208 (coe v0)) (coe d_get'45'rcx_210 (coe v0))
                  (coe d_get'45'rdx_212 (coe v0)) (coe d_get'45'rsi_214 (coe v0))
                  (coe d_get'45'rdi_216 (coe v0)) (coe d_get'45'rbp_218 (coe v0))
                  (coe d_get'45'rsp_220 (coe v0)) (coe d_get'45'r8_222 (coe v0))
                  (coe d_get'45'r9_224 (coe v0)) (coe d_get'45'r10_226 (coe v0))
                  (coe d_get'45'r11_228 (coe v0)) (coe d_get'45'r12_230 (coe v0))
                  (coe d_get'45'r13_232 (coe v0)) (coe d_get'45'r14_234 (coe v0))
                  (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.Addr
d_Addr_340 :: ()
d_Addr_340 = erased
-- Once.CCC.Target.X86-64.Semantics.Memory
d_Memory_342 :: ()
d_Memory_342 = erased
-- Once.CCC.Target.X86-64.Semantics.readMem
d_readMem_344 ::
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
d_readMem_344 v0 v1 = coe v0 v1
-- Once.CCC.Target.X86-64.Semantics.writeMem
d_writeMem_350 ::
  (Integer -> Maybe Integer) ->
  Integer -> Integer -> Integer -> Maybe Integer
d_writeMem_350 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v3) (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
      (coe v0 v3)
-- Once.CCC.Target.X86-64.Semantics.Flags
d_Flags_360 = ()
data T_Flags_360 = C_mkflags_374 Bool Bool Bool
-- Once.CCC.Target.X86-64.Semantics.Flags.zf
d_zf_368 :: T_Flags_360 -> Bool
d_zf_368 v0
  = case coe v0 of
      C_mkflags_374 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.Flags.cf
d_cf_370 :: T_Flags_360 -> Bool
d_cf_370 v0
  = case coe v0 of
      C_mkflags_374 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.Flags.sf
d_sf_372 :: T_Flags_360 -> Bool
d_sf_372 v0
  = case coe v0 of
      C_mkflags_374 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.State
d_State_376 = ()
data T_State_376
  = C_mkstate_398 T_RegFile_172 (Integer -> Maybe Integer)
                  T_Flags_360 Integer Bool
-- Once.CCC.Target.X86-64.Semantics.State.regs
d_regs_388 :: T_State_376 -> T_RegFile_172
d_regs_388 v0
  = case coe v0 of
      C_mkstate_398 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.State.memory
d_memory_390 :: T_State_376 -> Integer -> Maybe Integer
d_memory_390 v0
  = case coe v0 of
      C_mkstate_398 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.State.flags
d_flags_392 :: T_State_376 -> T_Flags_360
d_flags_392 v0
  = case coe v0 of
      C_mkstate_398 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.State.pc
d_pc_394 :: T_State_376 -> Integer
d_pc_394 v0
  = case coe v0 of
      C_mkstate_398 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.State.halted
d_halted_396 :: T_State_376 -> Bool
d_halted_396 v0
  = case coe v0 of
      C_mkstate_398 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.emptyMemory
d_emptyMemory_400 :: Integer -> Maybe Integer
d_emptyMemory_400 ~v0 = du_emptyMemory_400
du_emptyMemory_400 :: Maybe Integer
du_emptyMemory_400
  = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.CCC.Target.X86-64.Semantics.initFlags
d_initFlags_404 :: T_Flags_360
d_initFlags_404
  = coe
      C_mkflags_374 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.CCC.Target.X86-64.Semantics.stack-top
d_stack'45'top_406
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Target.X86-64.Semantics.stack-top"
-- Once.CCC.Target.X86-64.Semantics.emptyRegFile
d_emptyRegFile_408 :: T_RegFile_172
d_emptyRegFile_408
  = coe
      C_mkregfile_238 (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.initStateAt
d_initStateAt_410 :: Integer -> T_State_376
d_initStateAt_410 v0
  = coe
      C_mkstate_398
      (coe
         d_writeReg_274 d_emptyRegFile_408
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
         d_stack'45'top_406)
      (\ v1 -> coe du_emptyMemory_400) (coe d_initFlags_404) (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.CCC.Target.X86-64.Semantics.initState
d_initState_414 :: T_State_376
d_initState_414 = coe d_initStateAt_410 (coe (0 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.effectiveAddr
d_effectiveAddr_416 ::
  T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Mem_10 -> Integer
d_effectiveAddr_416 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_12 v2
        -> coe d_readReg_240 (coe d_regs_388 (coe v0)) (coe v2)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_14 v2 v3
        -> coe
             addInt (coe d_readReg_240 (coe d_regs_388 (coe v0)) (coe v2))
             (coe v3)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rip'43'disp_16 v2
        -> coe addInt (coe d_pc_394 (coe v0)) (coe v2)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rip'43'label_18 v2
        -> coe MAlonzo.Code.Once.CCC.Label.d_idx_18 (coe v2)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rip'43'sym_20 v2
        -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.readOperand
d_readOperand_438 ::
  T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Operand_22 ->
  Maybe Integer
d_readOperand_438 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe d_readReg_240 (coe d_regs_388 (coe v0)) (coe v2))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_26 v2
        -> coe
             d_readMem_344 (coe d_memory_390 (coe v0))
             (coe d_effectiveAddr_416 (coe v0) (coe v2))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_28 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.Word.d_norm_16 (coe (64 :: Integer)) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.writeOperand
d_writeOperand_452 ::
  T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Operand_22 ->
  Integer -> T_State_376
d_writeOperand_452 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkstate_398 (coe d_writeReg_274 (d_regs_388 (coe v0)) v2 v3)
                  (coe d_memory_390 (coe v0)) (coe d_flags_392 (coe v0))
                  (coe d_pc_394 (coe v0)) (coe d_halted_396 (coe v0)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_26 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkstate_398 (coe d_regs_388 (coe v0))
                  (coe
                     d_writeMem_350 (coe d_memory_390 (coe v0))
                     (coe d_effectiveAddr_416 (coe v0) (coe v2)) (coe v3))
                  (coe d_flags_392 (coe v0)) (coe d_pc_394 (coe v0))
                  (coe d_halted_396 (coe v0)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_28 v2
        -> coe (\ v3 -> v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.updateFlags
d_updateFlags_468 :: Integer -> Integer -> T_Flags_360
d_updateFlags_468 v0 ~v1 = du_updateFlags_468 v0
du_updateFlags_468 :: Integer -> T_Flags_360
du_updateFlags_468 v0
  = coe
      C_mkflags_374 (coe eqInt (coe v0) (coe (0 :: Integer)))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.CCC.Target.X86-64.Semantics._<ᵇ_
d__'60''7495'__472 :: Integer -> Integer -> Bool
d__'60''7495'__472 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe (coe d__'60''7495'__472 (coe v2) (coe v3)))
-- Once.CCC.Target.X86-64.Semantics.find-label-go
d_find'45'label'45'go_478 ::
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  Integer -> Maybe Integer
d_find'45'label'45'go_478 v0 v1 v2
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v3 v4
        -> let v5
                 = d_find'45'label'45'go_478
                     (coe v0) (coe v4) (coe addInt (coe (1 :: Integer)) (coe v2)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_70 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe
                          MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7480'__360 (coe v6)
                          (coe v0))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
                       (coe
                          d_find'45'label'45'go_478 (coe v0) (coe v4)
                          (coe addInt (coe (1 :: Integer)) (coe v2)))
                _ -> coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.find-label
d_find'45'label_496 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 -> Maybe Integer
d_find'45'label_496 v0 v1
  = coe
      d_find'45'label'45'go_478 (coe v1) (coe v0) (coe (0 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.execInstr
d_execInstr_502 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30 ->
  Maybe T_State_376
d_execInstr_502 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_32 v3 v4
        -> let v5 = d_readOperand_438 (coe v1) (coe v4) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_398 (coe d_regs_388 (coe d_writeOperand_452 v1 v3 v6))
                          (coe d_memory_390 (coe d_writeOperand_452 v1 v3 v6))
                          (coe d_flags_392 (coe d_writeOperand_452 v1 v3 v6))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_394 (coe v1)))
                          (coe d_halted_396 (coe d_writeOperand_452 v1 v3 v6)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_lea_34 v3 v4
        -> let v5
                 = coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe
                        C_mkstate_398
                        (coe
                           d_writeReg_274 (d_regs_388 (coe v1)) v3
                           (d_effectiveAddr_416 (coe v1) (coe v4)))
                        (coe d_memory_390 (coe v1)) (coe d_flags_392 (coe v1))
                        (coe addInt (coe (1 :: Integer)) (coe d_pc_394 (coe v1)))
                        (coe d_halted_396 (coe v1))) in
           coe
             (case coe v4 of
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rip'43'label_18 v6
                  -> let v7
                           = d_find'45'label_496
                               (coe v0)
                               (coe
                                  MAlonzo.Code.Once.CCC.Label.C_callee_34
                                  (coe MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v6))) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_398 (coe d_writeReg_274 (d_regs_388 (coe v1)) v3 v8)
                                    (coe d_memory_390 (coe v1)) (coe d_flags_392 (coe v1))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_394 (coe v1)))
                                    (coe d_halted_396 (coe v1)))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_398 (coe d_regs_388 (coe v1))
                                    (coe d_memory_390 (coe v1)) (coe d_flags_392 (coe v1))
                                    (coe d_pc_394 (coe v1))
                                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v5)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_36 v3 v4
        -> let v5 = d_readOperand_438 (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> let v7 = d_readOperand_438 (coe v1) (coe v4) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_398
                                    (coe
                                       d_regs_388
                                       (coe
                                          d_writeOperand_452 v1 v3
                                          (MAlonzo.Code.Once.Word.d__'8853'__26
                                             (coe (64 :: Integer)) (coe v6) (coe v8))))
                                    (coe
                                       d_memory_390
                                       (coe
                                          d_writeOperand_452 v1 v3
                                          (MAlonzo.Code.Once.Word.d__'8853'__26
                                             (coe (64 :: Integer)) (coe v6) (coe v8))))
                                    (coe
                                       du_updateFlags_468
                                       (coe
                                          MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer))
                                          (coe v6) (coe v8)))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_394 (coe v1)))
                                    (coe
                                       d_halted_396
                                       (coe
                                          d_writeOperand_452 v1 v3
                                          (MAlonzo.Code.Once.Word.d__'8853'__26
                                             (coe (64 :: Integer)) (coe v6) (coe v8)))))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_38 v3 v4
        -> let v5 = d_readOperand_438 (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> let v7 = d_readOperand_438 (coe v1) (coe v4) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_398
                                    (coe
                                       d_regs_388
                                       (coe
                                          d_writeOperand_452 v1 v3
                                          (MAlonzo.Code.Once.Word.d__'8854'__32
                                             (coe (64 :: Integer)) (coe v6) (coe v8))))
                                    (coe
                                       d_memory_390
                                       (coe
                                          d_writeOperand_452 v1 v3
                                          (MAlonzo.Code.Once.Word.d__'8854'__32
                                             (coe (64 :: Integer)) (coe v6) (coe v8))))
                                    (coe
                                       du_updateFlags_468
                                       (coe
                                          MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
                                          (coe v6) (coe v8)))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_394 (coe v1)))
                                    (coe
                                       d_halted_396
                                       (coe
                                          d_writeOperand_452 v1 v3
                                          (MAlonzo.Code.Once.Word.d__'8854'__32
                                             (coe (64 :: Integer)) (coe v6) (coe v8)))))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sbb_40 v3 v4
        -> let v5 = d_readOperand_438 (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> let v7 = d_readOperand_438 (coe v1) (coe v4) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_398
                                    (coe
                                       d_regs_388
                                       (coe
                                          d_writeOperand_452 v1 v3
                                          (MAlonzo.Code.Once.Word.d__'8854'__32
                                             (coe (64 :: Integer))
                                             (coe
                                                MAlonzo.Code.Once.Word.d__'8854'__32
                                                (coe (64 :: Integer)) (coe v6) (coe v8))
                                             (coe
                                                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                (coe d_cf_370 (coe d_flags_392 (coe v1)))
                                                (coe (1 :: Integer)) (coe (0 :: Integer))))))
                                    (coe
                                       d_memory_390
                                       (coe
                                          d_writeOperand_452 v1 v3
                                          (MAlonzo.Code.Once.Word.d__'8854'__32
                                             (coe (64 :: Integer))
                                             (coe
                                                MAlonzo.Code.Once.Word.d__'8854'__32
                                                (coe (64 :: Integer)) (coe v6) (coe v8))
                                             (coe
                                                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                (coe d_cf_370 (coe d_flags_392 (coe v1)))
                                                (coe (1 :: Integer)) (coe (0 :: Integer))))))
                                    (coe
                                       du_updateFlags_468
                                       (coe
                                          MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
                                          (coe
                                             MAlonzo.Code.Once.Word.d__'8854'__32
                                             (coe (64 :: Integer)) (coe v6) (coe v8))
                                          (coe
                                             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                             (coe d_cf_370 (coe d_flags_392 (coe v1)))
                                             (coe (1 :: Integer)) (coe (0 :: Integer)))))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_394 (coe v1)))
                                    (coe
                                       d_halted_396
                                       (coe
                                          d_writeOperand_452 v1 v3
                                          (MAlonzo.Code.Once.Word.d__'8854'__32
                                             (coe (64 :: Integer))
                                             (coe
                                                MAlonzo.Code.Once.Word.d__'8854'__32
                                                (coe (64 :: Integer)) (coe v6) (coe v8))
                                             (coe
                                                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                (coe d_cf_370 (coe d_flags_392 (coe v1)))
                                                (coe (1 :: Integer)) (coe (0 :: Integer)))))))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_cmp_42 v3 v4
        -> let v5 = d_readOperand_438 (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> let v7 = d_readOperand_438 (coe v1) (coe v4) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_398 (coe d_regs_388 (coe v1))
                                    (coe d_memory_390 (coe v1))
                                    (coe
                                       C_mkflags_374 (coe eqInt (coe v6) (coe v8))
                                       (coe d__'60''7495'__472 (coe v6) (coe v8))
                                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_394 (coe v1)))
                                    (coe d_halted_396 (coe v1)))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_test_44 v3 v4
        -> let v5 = d_readOperand_438 (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> let v7 = d_readOperand_438 (coe v1) (coe v4) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_398 (coe d_regs_388 (coe v1))
                                    (coe d_memory_390 (coe v1))
                                    (coe
                                       C_mkflags_374 (coe eqInt (coe v6) (coe (0 :: Integer)))
                                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_394 (coe v1)))
                                    (coe d_halted_396 (coe v1)))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jmp_46 v3
        -> let v4 = d_find'45'label_496 (coe v0) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_398 (coe d_regs_388 (coe v1)) (coe d_memory_390 (coe v1))
                          (coe d_flags_392 (coe v1)) (coe v5) (coe d_halted_396 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_398 (coe d_regs_388 (coe v1)) (coe d_memory_390 (coe v1))
                          (coe d_flags_392 (coe v1)) (coe d_pc_394 (coe v1))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_je_48 v3
        -> let v4 = d_zf_368 (coe d_flags_392 (coe v1)) in
           coe
             (if coe v4
                then let v5 = d_find'45'label_496 (coe v0) (coe v3) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_398 (coe d_regs_388 (coe v1))
                                    (coe d_memory_390 (coe v1)) (coe d_flags_392 (coe v1)) (coe v6)
                                    (coe d_halted_396 (coe v1)))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_398 (coe d_regs_388 (coe v1))
                                    (coe d_memory_390 (coe v1)) (coe d_flags_392 (coe v1))
                                    (coe d_pc_394 (coe v1)) (coe v4))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                else coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_398 (coe d_regs_388 (coe v1)) (coe d_memory_390 (coe v1))
                          (coe d_flags_392 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_394 (coe v1)))
                          (coe d_halted_396 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jne_50 v3
        -> let v4 = d_zf_368 (coe d_flags_392 (coe v1)) in
           coe
             (if coe v4
                then coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_398 (coe d_regs_388 (coe v1)) (coe d_memory_390 (coe v1))
                          (coe d_flags_392 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_394 (coe v1)))
                          (coe d_halted_396 (coe v1)))
                else (let v5 = d_find'45'label_496 (coe v0) (coe v3) in
                      coe
                        (case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                  (coe
                                     C_mkstate_398 (coe d_regs_388 (coe v1))
                                     (coe d_memory_390 (coe v1)) (coe d_flags_392 (coe v1)) (coe v6)
                                     (coe d_halted_396 (coe v1)))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                  (coe
                                     C_mkstate_398 (coe d_regs_388 (coe v1))
                                     (coe d_memory_390 (coe v1)) (coe d_flags_392 (coe v1))
                                     (coe d_pc_394 (coe v1))
                                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call_52 v3
        -> let v4 = d_readOperand_438 (coe v1) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_398
                          (coe
                             d_writeReg_274 (d_regs_388 (coe v1))
                             (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_240
                                   (coe d_regs_388 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86))
                          (coe
                             d_writeMem_350 (coe d_memory_390 (coe v1))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_240
                                   (coe d_regs_388 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86)
                             (coe addInt (coe (1 :: Integer)) (coe d_pc_394 (coe v1))))
                          (coe d_flags_392 (coe v1)) (coe v5) (coe d_halted_396 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call'45'sym_54 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_398 (coe d_regs_388 (coe v1)) (coe d_memory_390 (coe v1))
                (coe d_flags_392 (coe v1)) (coe d_pc_394 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call'45'l_56 v3
        -> let v4 = d_find'45'label_496 (coe v0) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_398
                          (coe
                             d_writeReg_274 (d_regs_388 (coe v1))
                             (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_240
                                   (coe d_regs_388 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86))
                          (coe
                             d_writeMem_350 (coe d_memory_390 (coe v1))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_240
                                   (coe d_regs_388 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86)
                             (coe addInt (coe (1 :: Integer)) (coe d_pc_394 (coe v1))))
                          (coe d_flags_392 (coe v1)) (coe v5) (coe d_halted_396 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_398 (coe d_regs_388 (coe v1)) (coe d_memory_390 (coe v1))
                          (coe d_flags_392 (coe v1)) (coe d_pc_394 (coe v1))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ret_58
        -> let v3
                 = d_readMem_344
                     (coe d_memory_390 (coe v1))
                     (coe
                        d_readReg_240 (coe d_regs_388 (coe v1))
                        (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_398
                          (coe
                             d_writeReg_274 (d_regs_388 (coe v1))
                             (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
                             (addInt
                                (coe
                                   d_readReg_240 (coe d_regs_388 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86)))
                          (coe d_memory_390 (coe v1)) (coe d_flags_392 (coe v1)) (coe v4)
                          (coe d_halted_396 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_push_60 v3
        -> let v4 = d_readOperand_438 (coe v1) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_398
                          (coe
                             d_writeReg_274 (d_regs_388 (coe v1))
                             (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_240
                                   (coe d_regs_388 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86))
                          (coe
                             d_writeMem_350 (coe d_memory_390 (coe v1))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_240
                                   (coe d_regs_388 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86)
                             (coe v5))
                          (coe d_flags_392 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_394 (coe v1)))
                          (coe d_halted_396 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_pop_62 v3
        -> let v4
                 = d_readMem_344
                     (coe d_memory_390 (coe v1))
                     (coe
                        d_readReg_240 (coe d_regs_388 (coe v1))
                        (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_398
                          (coe
                             d_writeReg_274 (coe d_writeReg_274 (d_regs_388 (coe v1)) v3 v5)
                             (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
                             (addInt
                                (coe
                                   d_readReg_240 (coe d_regs_388 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86)))
                          (coe d_memory_390 (coe v1)) (coe d_flags_392 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_394 (coe v1)))
                          (coe d_halted_396 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_nop_64
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_398 (coe d_regs_388 (coe v1)) (coe d_memory_390 (coe v1))
                (coe d_flags_392 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_394 (coe v1)))
                (coe d_halted_396 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_66
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_398 (coe d_regs_388 (coe v1)) (coe d_memory_390 (coe v1))
                (coe d_flags_392 (coe v1)) (coe d_pc_394 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_syscall_68
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_398 (coe d_regs_388 (coe v1)) (coe d_memory_390 (coe v1))
                (coe d_flags_392 (coe v1)) (coe d_pc_394 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_70 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_398 (coe d_regs_388 (coe v1)) (coe d_memory_390 (coe v1))
                (coe d_flags_392 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_394 (coe v1)))
                (coe d_halted_396 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.fetch
d_fetch_770 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30
d_fetch_770 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe d_fetch_770 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.step-not-halted
d_step'45'not'45'halted_778 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  T_State_376 -> Maybe T_State_376
d_step'45'not'45'halted_778 v0 v1
  = let v2 = d_fetch_770 (coe v0) (coe d_pc_394 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe d_execInstr_502 (coe v0) (coe v1) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   C_mkstate_398 (coe d_regs_388 (coe v1)) (coe d_memory_390 (coe v1))
                   (coe d_flags_392 (coe v1)) (coe d_pc_394 (coe v1))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Target.X86-64.Semantics.step
d_step_788 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  T_State_376 -> Maybe T_State_376
d_step_788 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_halted_396 (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1))
      (coe d_step'45'not'45'halted_778 (coe v0) (coe v1))
-- Once.CCC.Target.X86-64.Semantics.exec
d_exec_794 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  T_State_376 -> Maybe T_State_376
d_exec_794 v0 v1 v2
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe d_halted_396 (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
                (coe
                   d_exec'45'cont_796 (coe v3) (coe v1)
                   (coe d_step'45'not'45'halted_778 (coe v1) (coe v2))))
-- Once.CCC.Target.X86-64.Semantics.exec-cont
d_exec'45'cont_796 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  Maybe T_State_376 -> Maybe T_State_376
d_exec'45'cont_796 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_halted_396 (coe v3)) (coe v2)
             (coe d_exec_794 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.defaultFuel
d_defaultFuel_812 :: Integer
d_defaultFuel_812 = coe (10000 :: Integer)
-- Once.CCC.Target.X86-64.Semantics.run
d_run_814 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  T_State_376 -> Maybe T_State_376
d_run_814 = coe d_exec_794 (coe d_defaultFuel_812)
