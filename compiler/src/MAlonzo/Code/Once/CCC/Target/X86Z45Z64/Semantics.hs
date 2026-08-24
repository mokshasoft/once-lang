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
-- Once.CCC.Target.X86-64.Semantics.W.sdiv2ᵏ
d_sdiv2'7503'_114 :: Integer -> Integer -> Integer
d_sdiv2'7503'_114
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_138 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.shlᵂ
d_shl'7490'_116 :: Integer -> Integer -> Integer
d_shl'7490'_116
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_132 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.sucNegOne≡mod
d_sucNegOne'8801'mod_118 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_118 = erased
-- Once.CCC.Target.X86-64.Semantics.W.tdiv-neg1
d_tdiv'45'neg1_120 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_120 = erased
-- Once.CCC.Target.X86-64.Semantics.W.tmod-neg1
d_tmod'45'neg1_122 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_122 = erased
-- Once.CCC.Target.X86-64.Semantics.W.toWord
d_toWord_124 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_124 v0 v1
  = coe MAlonzo.Code.Once.Word.du_toWord_68 (coe (64 :: Integer)) v0
-- Once.CCC.Target.X86-64.Semantics.W.toWord≡fromℤ
d_toWord'8801'fromℤ_126 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'8801'fromℤ_126 = erased
-- Once.CCC.Target.X86-64.Semantics.W.toℤ
d_toℤ_128 :: Integer -> Integer
d_toℤ_128
  = coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.toℤ-negOne
d_toℤ'45'negOne_130 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_130 = erased
-- Once.CCC.Target.X86-64.Semantics.W.toℤ∘fromℤ
d_toℤ'8728'fromℤ_132 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'8728'fromℤ_132 = erased
-- Once.CCC.Target.X86-64.Semantics.W.unplus
d_unplus_134 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_unplus_134 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Word.du_unplus_648 v4
-- Once.CCC.Target.X86-64.Semantics.W.≡ᵇ-refl
d_'8801''7495''45'refl_136 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_136 = erased
-- Once.CCC.Target.X86-64.Semantics.W.≡ᵇ0-false
d_'8801''7495'0'45'false_138 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_138 = erased
-- Once.CCC.Target.X86-64.Semantics.W.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_140 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_140 = erased
-- Once.CCC.Target.X86-64.Semantics.W.⊕-neg
d_'8853''45'neg_142 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_142 = erased
-- Once.CCC.Target.X86-64.Semantics.W.⊕-neg-suc
d_'8853''45'neg'45'suc_144 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_144 = erased
-- Once.CCC.Target.X86-64.Semantics.W.⊕-normʳ
d_'8853''45'norm'691'_146 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_146 = erased
-- Once.CCC.Target.X86-64.Semantics.W.⊕≡+
d_'8853''8801''43'_148 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_148 = erased
-- Once.CCC.Target.X86-64.Semantics.W.⊖-normʳ
d_'8854''45'norm'691'_150 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_150 = erased
-- Once.CCC.Target.X86-64.Semantics.W.⊖≡∸
d_'8854''8801''8760'_152 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_152 = erased
-- Once.CCC.Target.X86-64.Semantics.W.⊗-pow2
d_'8855''45'pow2_154 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_154 = erased
-- Once.CCC.Target.X86-64.Semantics.W.⊝_
d_'8861'__156 :: Integer -> Integer
d_'8861'__156
  = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.W.⊝-fromℤ
d_'8861''45'fromℤ_158 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'fromℤ_158 = erased
-- Once.CCC.Target.X86-64.Semantics.W.⊝-intMin
d_'8861''45'intMin_160 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_160 = erased
-- Once.CCC.Target.X86-64.Semantics.W.⊝-invol-norm
d_'8861''45'invol'45'norm_162 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'invol'45'norm_162 = erased
-- Once.CCC.Target.X86-64.Semantics.Word
d_Word_164 :: ()
d_Word_164 = erased
-- Once.CCC.Target.X86-64.Semantics.RegFile
d_RegFile_166 = ()
data T_RegFile_166
  = C_mkregfile_232 Integer Integer Integer Integer Integer Integer
                    Integer Integer Integer Integer Integer Integer Integer Integer
                    Integer Integer
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rax
d_get'45'rax_200 :: T_RegFile_166 -> Integer
d_get'45'rax_200 v0
  = case coe v0 of
      C_mkregfile_232 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rbx
d_get'45'rbx_202 :: T_RegFile_166 -> Integer
d_get'45'rbx_202 v0
  = case coe v0 of
      C_mkregfile_232 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rcx
d_get'45'rcx_204 :: T_RegFile_166 -> Integer
d_get'45'rcx_204 v0
  = case coe v0 of
      C_mkregfile_232 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rdx
d_get'45'rdx_206 :: T_RegFile_166 -> Integer
d_get'45'rdx_206 v0
  = case coe v0 of
      C_mkregfile_232 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rsi
d_get'45'rsi_208 :: T_RegFile_166 -> Integer
d_get'45'rsi_208 v0
  = case coe v0 of
      C_mkregfile_232 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rdi
d_get'45'rdi_210 :: T_RegFile_166 -> Integer
d_get'45'rdi_210 v0
  = case coe v0 of
      C_mkregfile_232 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rbp
d_get'45'rbp_212 :: T_RegFile_166 -> Integer
d_get'45'rbp_212 v0
  = case coe v0 of
      C_mkregfile_232 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rsp
d_get'45'rsp_214 :: T_RegFile_166 -> Integer
d_get'45'rsp_214 v0
  = case coe v0 of
      C_mkregfile_232 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r8
d_get'45'r8_216 :: T_RegFile_166 -> Integer
d_get'45'r8_216 v0
  = case coe v0 of
      C_mkregfile_232 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r9
d_get'45'r9_218 :: T_RegFile_166 -> Integer
d_get'45'r9_218 v0
  = case coe v0 of
      C_mkregfile_232 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r10
d_get'45'r10_220 :: T_RegFile_166 -> Integer
d_get'45'r10_220 v0
  = case coe v0 of
      C_mkregfile_232 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r11
d_get'45'r11_222 :: T_RegFile_166 -> Integer
d_get'45'r11_222 v0
  = case coe v0 of
      C_mkregfile_232 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r12
d_get'45'r12_224 :: T_RegFile_166 -> Integer
d_get'45'r12_224 v0
  = case coe v0 of
      C_mkregfile_232 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r13
d_get'45'r13_226 :: T_RegFile_166 -> Integer
d_get'45'r13_226 v0
  = case coe v0 of
      C_mkregfile_232 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r14
d_get'45'r14_228 :: T_RegFile_166 -> Integer
d_get'45'r14_228 v0
  = case coe v0 of
      C_mkregfile_232 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r15
d_get'45'r15_230 :: T_RegFile_166 -> Integer
d_get'45'r15_230 v0
  = case coe v0 of
      C_mkregfile_232 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.readReg
d_readReg_234 ::
  T_RegFile_166 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer
d_readReg_234 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10
        -> coe d_get'45'rax_200 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12
        -> coe d_get'45'rbx_202 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rcx_14
        -> coe d_get'45'rcx_204 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdx_16
        -> coe d_get'45'rdx_206 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsi_18
        -> coe d_get'45'rsi_208 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20
        -> coe d_get'45'rdi_210 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbp_22
        -> coe d_get'45'rbp_212 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24
        -> coe d_get'45'rsp_214 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r8_26
        -> coe d_get'45'r8_216 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r9_28
        -> coe d_get'45'r9_218 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r10_30
        -> coe d_get'45'r10_220 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r11_32
        -> coe d_get'45'r11_222 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r12_34
        -> coe d_get'45'r12_224 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r13_36
        -> coe d_get'45'r13_226 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r14_38
        -> coe d_get'45'r14_228 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r15_40
        -> coe d_get'45'r15_230 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.writeReg
d_writeReg_268 ::
  T_RegFile_166 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer -> T_RegFile_166
d_writeReg_268 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_232 (coe v2) (coe d_get'45'rbx_202 (coe v0))
                  (coe d_get'45'rcx_204 (coe v0)) (coe d_get'45'rdx_206 (coe v0))
                  (coe d_get'45'rsi_208 (coe v0)) (coe d_get'45'rdi_210 (coe v0))
                  (coe d_get'45'rbp_212 (coe v0)) (coe d_get'45'rsp_214 (coe v0))
                  (coe d_get'45'r8_216 (coe v0)) (coe d_get'45'r9_218 (coe v0))
                  (coe d_get'45'r10_220 (coe v0)) (coe d_get'45'r11_222 (coe v0))
                  (coe d_get'45'r12_224 (coe v0)) (coe d_get'45'r13_226 (coe v0))
                  (coe d_get'45'r14_228 (coe v0)) (coe d_get'45'r15_230 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_232 (coe d_get'45'rax_200 (coe v0)) (coe v2)
                  (coe d_get'45'rcx_204 (coe v0)) (coe d_get'45'rdx_206 (coe v0))
                  (coe d_get'45'rsi_208 (coe v0)) (coe d_get'45'rdi_210 (coe v0))
                  (coe d_get'45'rbp_212 (coe v0)) (coe d_get'45'rsp_214 (coe v0))
                  (coe d_get'45'r8_216 (coe v0)) (coe d_get'45'r9_218 (coe v0))
                  (coe d_get'45'r10_220 (coe v0)) (coe d_get'45'r11_222 (coe v0))
                  (coe d_get'45'r12_224 (coe v0)) (coe d_get'45'r13_226 (coe v0))
                  (coe d_get'45'r14_228 (coe v0)) (coe d_get'45'r15_230 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rcx_14
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_232 (coe d_get'45'rax_200 (coe v0))
                  (coe d_get'45'rbx_202 (coe v0)) (coe v2)
                  (coe d_get'45'rdx_206 (coe v0)) (coe d_get'45'rsi_208 (coe v0))
                  (coe d_get'45'rdi_210 (coe v0)) (coe d_get'45'rbp_212 (coe v0))
                  (coe d_get'45'rsp_214 (coe v0)) (coe d_get'45'r8_216 (coe v0))
                  (coe d_get'45'r9_218 (coe v0)) (coe d_get'45'r10_220 (coe v0))
                  (coe d_get'45'r11_222 (coe v0)) (coe d_get'45'r12_224 (coe v0))
                  (coe d_get'45'r13_226 (coe v0)) (coe d_get'45'r14_228 (coe v0))
                  (coe d_get'45'r15_230 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdx_16
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_232 (coe d_get'45'rax_200 (coe v0))
                  (coe d_get'45'rbx_202 (coe v0)) (coe d_get'45'rcx_204 (coe v0))
                  (coe v2) (coe d_get'45'rsi_208 (coe v0))
                  (coe d_get'45'rdi_210 (coe v0)) (coe d_get'45'rbp_212 (coe v0))
                  (coe d_get'45'rsp_214 (coe v0)) (coe d_get'45'r8_216 (coe v0))
                  (coe d_get'45'r9_218 (coe v0)) (coe d_get'45'r10_220 (coe v0))
                  (coe d_get'45'r11_222 (coe v0)) (coe d_get'45'r12_224 (coe v0))
                  (coe d_get'45'r13_226 (coe v0)) (coe d_get'45'r14_228 (coe v0))
                  (coe d_get'45'r15_230 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsi_18
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_232 (coe d_get'45'rax_200 (coe v0))
                  (coe d_get'45'rbx_202 (coe v0)) (coe d_get'45'rcx_204 (coe v0))
                  (coe d_get'45'rdx_206 (coe v0)) (coe v2)
                  (coe d_get'45'rdi_210 (coe v0)) (coe d_get'45'rbp_212 (coe v0))
                  (coe d_get'45'rsp_214 (coe v0)) (coe d_get'45'r8_216 (coe v0))
                  (coe d_get'45'r9_218 (coe v0)) (coe d_get'45'r10_220 (coe v0))
                  (coe d_get'45'r11_222 (coe v0)) (coe d_get'45'r12_224 (coe v0))
                  (coe d_get'45'r13_226 (coe v0)) (coe d_get'45'r14_228 (coe v0))
                  (coe d_get'45'r15_230 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_232 (coe d_get'45'rax_200 (coe v0))
                  (coe d_get'45'rbx_202 (coe v0)) (coe d_get'45'rcx_204 (coe v0))
                  (coe d_get'45'rdx_206 (coe v0)) (coe d_get'45'rsi_208 (coe v0))
                  (coe v2) (coe d_get'45'rbp_212 (coe v0))
                  (coe d_get'45'rsp_214 (coe v0)) (coe d_get'45'r8_216 (coe v0))
                  (coe d_get'45'r9_218 (coe v0)) (coe d_get'45'r10_220 (coe v0))
                  (coe d_get'45'r11_222 (coe v0)) (coe d_get'45'r12_224 (coe v0))
                  (coe d_get'45'r13_226 (coe v0)) (coe d_get'45'r14_228 (coe v0))
                  (coe d_get'45'r15_230 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbp_22
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_232 (coe d_get'45'rax_200 (coe v0))
                  (coe d_get'45'rbx_202 (coe v0)) (coe d_get'45'rcx_204 (coe v0))
                  (coe d_get'45'rdx_206 (coe v0)) (coe d_get'45'rsi_208 (coe v0))
                  (coe d_get'45'rdi_210 (coe v0)) (coe v2)
                  (coe d_get'45'rsp_214 (coe v0)) (coe d_get'45'r8_216 (coe v0))
                  (coe d_get'45'r9_218 (coe v0)) (coe d_get'45'r10_220 (coe v0))
                  (coe d_get'45'r11_222 (coe v0)) (coe d_get'45'r12_224 (coe v0))
                  (coe d_get'45'r13_226 (coe v0)) (coe d_get'45'r14_228 (coe v0))
                  (coe d_get'45'r15_230 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_232 (coe d_get'45'rax_200 (coe v0))
                  (coe d_get'45'rbx_202 (coe v0)) (coe d_get'45'rcx_204 (coe v0))
                  (coe d_get'45'rdx_206 (coe v0)) (coe d_get'45'rsi_208 (coe v0))
                  (coe d_get'45'rdi_210 (coe v0)) (coe d_get'45'rbp_212 (coe v0))
                  (coe v2) (coe d_get'45'r8_216 (coe v0))
                  (coe d_get'45'r9_218 (coe v0)) (coe d_get'45'r10_220 (coe v0))
                  (coe d_get'45'r11_222 (coe v0)) (coe d_get'45'r12_224 (coe v0))
                  (coe d_get'45'r13_226 (coe v0)) (coe d_get'45'r14_228 (coe v0))
                  (coe d_get'45'r15_230 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r8_26
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_232 (coe d_get'45'rax_200 (coe v0))
                  (coe d_get'45'rbx_202 (coe v0)) (coe d_get'45'rcx_204 (coe v0))
                  (coe d_get'45'rdx_206 (coe v0)) (coe d_get'45'rsi_208 (coe v0))
                  (coe d_get'45'rdi_210 (coe v0)) (coe d_get'45'rbp_212 (coe v0))
                  (coe d_get'45'rsp_214 (coe v0)) (coe v2)
                  (coe d_get'45'r9_218 (coe v0)) (coe d_get'45'r10_220 (coe v0))
                  (coe d_get'45'r11_222 (coe v0)) (coe d_get'45'r12_224 (coe v0))
                  (coe d_get'45'r13_226 (coe v0)) (coe d_get'45'r14_228 (coe v0))
                  (coe d_get'45'r15_230 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r9_28
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_232 (coe d_get'45'rax_200 (coe v0))
                  (coe d_get'45'rbx_202 (coe v0)) (coe d_get'45'rcx_204 (coe v0))
                  (coe d_get'45'rdx_206 (coe v0)) (coe d_get'45'rsi_208 (coe v0))
                  (coe d_get'45'rdi_210 (coe v0)) (coe d_get'45'rbp_212 (coe v0))
                  (coe d_get'45'rsp_214 (coe v0)) (coe d_get'45'r8_216 (coe v0))
                  (coe v2) (coe d_get'45'r10_220 (coe v0))
                  (coe d_get'45'r11_222 (coe v0)) (coe d_get'45'r12_224 (coe v0))
                  (coe d_get'45'r13_226 (coe v0)) (coe d_get'45'r14_228 (coe v0))
                  (coe d_get'45'r15_230 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r10_30
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_232 (coe d_get'45'rax_200 (coe v0))
                  (coe d_get'45'rbx_202 (coe v0)) (coe d_get'45'rcx_204 (coe v0))
                  (coe d_get'45'rdx_206 (coe v0)) (coe d_get'45'rsi_208 (coe v0))
                  (coe d_get'45'rdi_210 (coe v0)) (coe d_get'45'rbp_212 (coe v0))
                  (coe d_get'45'rsp_214 (coe v0)) (coe d_get'45'r8_216 (coe v0))
                  (coe d_get'45'r9_218 (coe v0)) (coe v2)
                  (coe d_get'45'r11_222 (coe v0)) (coe d_get'45'r12_224 (coe v0))
                  (coe d_get'45'r13_226 (coe v0)) (coe d_get'45'r14_228 (coe v0))
                  (coe d_get'45'r15_230 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r11_32
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_232 (coe d_get'45'rax_200 (coe v0))
                  (coe d_get'45'rbx_202 (coe v0)) (coe d_get'45'rcx_204 (coe v0))
                  (coe d_get'45'rdx_206 (coe v0)) (coe d_get'45'rsi_208 (coe v0))
                  (coe d_get'45'rdi_210 (coe v0)) (coe d_get'45'rbp_212 (coe v0))
                  (coe d_get'45'rsp_214 (coe v0)) (coe d_get'45'r8_216 (coe v0))
                  (coe d_get'45'r9_218 (coe v0)) (coe d_get'45'r10_220 (coe v0))
                  (coe v2) (coe d_get'45'r12_224 (coe v0))
                  (coe d_get'45'r13_226 (coe v0)) (coe d_get'45'r14_228 (coe v0))
                  (coe d_get'45'r15_230 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r12_34
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_232 (coe d_get'45'rax_200 (coe v0))
                  (coe d_get'45'rbx_202 (coe v0)) (coe d_get'45'rcx_204 (coe v0))
                  (coe d_get'45'rdx_206 (coe v0)) (coe d_get'45'rsi_208 (coe v0))
                  (coe d_get'45'rdi_210 (coe v0)) (coe d_get'45'rbp_212 (coe v0))
                  (coe d_get'45'rsp_214 (coe v0)) (coe d_get'45'r8_216 (coe v0))
                  (coe d_get'45'r9_218 (coe v0)) (coe d_get'45'r10_220 (coe v0))
                  (coe d_get'45'r11_222 (coe v0)) (coe v2)
                  (coe d_get'45'r13_226 (coe v0)) (coe d_get'45'r14_228 (coe v0))
                  (coe d_get'45'r15_230 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r13_36
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_232 (coe d_get'45'rax_200 (coe v0))
                  (coe d_get'45'rbx_202 (coe v0)) (coe d_get'45'rcx_204 (coe v0))
                  (coe d_get'45'rdx_206 (coe v0)) (coe d_get'45'rsi_208 (coe v0))
                  (coe d_get'45'rdi_210 (coe v0)) (coe d_get'45'rbp_212 (coe v0))
                  (coe d_get'45'rsp_214 (coe v0)) (coe d_get'45'r8_216 (coe v0))
                  (coe d_get'45'r9_218 (coe v0)) (coe d_get'45'r10_220 (coe v0))
                  (coe d_get'45'r11_222 (coe v0)) (coe d_get'45'r12_224 (coe v0))
                  (coe v2) (coe d_get'45'r14_228 (coe v0))
                  (coe d_get'45'r15_230 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r14_38
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_232 (coe d_get'45'rax_200 (coe v0))
                  (coe d_get'45'rbx_202 (coe v0)) (coe d_get'45'rcx_204 (coe v0))
                  (coe d_get'45'rdx_206 (coe v0)) (coe d_get'45'rsi_208 (coe v0))
                  (coe d_get'45'rdi_210 (coe v0)) (coe d_get'45'rbp_212 (coe v0))
                  (coe d_get'45'rsp_214 (coe v0)) (coe d_get'45'r8_216 (coe v0))
                  (coe d_get'45'r9_218 (coe v0)) (coe d_get'45'r10_220 (coe v0))
                  (coe d_get'45'r11_222 (coe v0)) (coe d_get'45'r12_224 (coe v0))
                  (coe d_get'45'r13_226 (coe v0)) (coe v2)
                  (coe d_get'45'r15_230 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r15_40
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_232 (coe d_get'45'rax_200 (coe v0))
                  (coe d_get'45'rbx_202 (coe v0)) (coe d_get'45'rcx_204 (coe v0))
                  (coe d_get'45'rdx_206 (coe v0)) (coe d_get'45'rsi_208 (coe v0))
                  (coe d_get'45'rdi_210 (coe v0)) (coe d_get'45'rbp_212 (coe v0))
                  (coe d_get'45'rsp_214 (coe v0)) (coe d_get'45'r8_216 (coe v0))
                  (coe d_get'45'r9_218 (coe v0)) (coe d_get'45'r10_220 (coe v0))
                  (coe d_get'45'r11_222 (coe v0)) (coe d_get'45'r12_224 (coe v0))
                  (coe d_get'45'r13_226 (coe v0)) (coe d_get'45'r14_228 (coe v0))
                  (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.Addr
d_Addr_334 :: ()
d_Addr_334 = erased
-- Once.CCC.Target.X86-64.Semantics.Memory
d_Memory_336 :: ()
d_Memory_336 = erased
-- Once.CCC.Target.X86-64.Semantics.readMem
d_readMem_338 ::
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
d_readMem_338 v0 v1 = coe v0 v1
-- Once.CCC.Target.X86-64.Semantics.writeMem
d_writeMem_344 ::
  (Integer -> Maybe Integer) ->
  Integer -> Integer -> Integer -> Maybe Integer
d_writeMem_344 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v3) (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
      (coe v0 v3)
-- Once.CCC.Target.X86-64.Semantics.Flags
d_Flags_354 = ()
data T_Flags_354 = C_mkflags_368 Bool Bool Bool
-- Once.CCC.Target.X86-64.Semantics.Flags.zf
d_zf_362 :: T_Flags_354 -> Bool
d_zf_362 v0
  = case coe v0 of
      C_mkflags_368 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.Flags.cf
d_cf_364 :: T_Flags_354 -> Bool
d_cf_364 v0
  = case coe v0 of
      C_mkflags_368 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.Flags.sf
d_sf_366 :: T_Flags_354 -> Bool
d_sf_366 v0
  = case coe v0 of
      C_mkflags_368 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.State
d_State_370 = ()
data T_State_370
  = C_mkstate_392 T_RegFile_166 (Integer -> Maybe Integer)
                  T_Flags_354 Integer Bool
-- Once.CCC.Target.X86-64.Semantics.State.regs
d_regs_382 :: T_State_370 -> T_RegFile_166
d_regs_382 v0
  = case coe v0 of
      C_mkstate_392 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.State.memory
d_memory_384 :: T_State_370 -> Integer -> Maybe Integer
d_memory_384 v0
  = case coe v0 of
      C_mkstate_392 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.State.flags
d_flags_386 :: T_State_370 -> T_Flags_354
d_flags_386 v0
  = case coe v0 of
      C_mkstate_392 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.State.pc
d_pc_388 :: T_State_370 -> Integer
d_pc_388 v0
  = case coe v0 of
      C_mkstate_392 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.State.halted
d_halted_390 :: T_State_370 -> Bool
d_halted_390 v0
  = case coe v0 of
      C_mkstate_392 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.emptyMemory
d_emptyMemory_394 :: Integer -> Maybe Integer
d_emptyMemory_394 ~v0 = du_emptyMemory_394
du_emptyMemory_394 :: Maybe Integer
du_emptyMemory_394
  = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.CCC.Target.X86-64.Semantics.initFlags
d_initFlags_398 :: T_Flags_354
d_initFlags_398
  = coe
      C_mkflags_368 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.CCC.Target.X86-64.Semantics.stack-top
d_stack'45'top_400
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Target.X86-64.Semantics.stack-top"
-- Once.CCC.Target.X86-64.Semantics.emptyRegFile
d_emptyRegFile_402 :: T_RegFile_166
d_emptyRegFile_402
  = coe
      C_mkregfile_232 (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.initState
d_initState_404 :: T_State_370
d_initState_404
  = coe
      C_mkstate_392
      (coe
         d_writeReg_268 d_emptyRegFile_402
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
         d_stack'45'top_400)
      (\ v0 -> coe du_emptyMemory_394) (coe d_initFlags_398)
      (coe (0 :: Integer)) (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.CCC.Target.X86-64.Semantics.effectiveAddr
d_effectiveAddr_406 ::
  T_State_370 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Mem_10 -> Integer
d_effectiveAddr_406 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_12 v2
        -> coe d_readReg_234 (coe d_regs_382 (coe v0)) (coe v2)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_14 v2 v3
        -> coe
             addInt (coe d_readReg_234 (coe d_regs_382 (coe v0)) (coe v2))
             (coe v3)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rip'43'disp_16 v2
        -> coe addInt (coe d_pc_388 (coe v0)) (coe v2)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rip'43'label_18 v2
        -> coe MAlonzo.Code.Once.CCC.Label.d_idx_18 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.readOperand
d_readOperand_426 ::
  T_State_370 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Operand_20 ->
  Maybe Integer
d_readOperand_426 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_22 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe d_readReg_234 (coe d_regs_382 (coe v0)) (coe v2))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_24 v2
        -> coe
             d_readMem_338 (coe d_memory_384 (coe v0))
             (coe d_effectiveAddr_406 (coe v0) (coe v2))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_26 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.Word.d_norm_16 (coe (64 :: Integer)) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.writeOperand
d_writeOperand_440 ::
  T_State_370 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Operand_20 ->
  Integer -> T_State_370
d_writeOperand_440 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_22 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkstate_392 (coe d_writeReg_268 (d_regs_382 (coe v0)) v2 v3)
                  (coe d_memory_384 (coe v0)) (coe d_flags_386 (coe v0))
                  (coe d_pc_388 (coe v0)) (coe d_halted_390 (coe v0)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_24 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkstate_392 (coe d_regs_382 (coe v0))
                  (coe
                     d_writeMem_344 (coe d_memory_384 (coe v0))
                     (coe d_effectiveAddr_406 (coe v0) (coe v2)) (coe v3))
                  (coe d_flags_386 (coe v0)) (coe d_pc_388 (coe v0))
                  (coe d_halted_390 (coe v0)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_26 v2
        -> coe (\ v3 -> v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.updateFlags
d_updateFlags_456 :: Integer -> Integer -> T_Flags_354
d_updateFlags_456 v0 ~v1 = du_updateFlags_456 v0
du_updateFlags_456 :: Integer -> T_Flags_354
du_updateFlags_456 v0
  = coe
      C_mkflags_368 (coe eqInt (coe v0) (coe (0 :: Integer)))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.CCC.Target.X86-64.Semantics._<ᵇ_
d__'60''7495'__460 :: Integer -> Integer -> Bool
d__'60''7495'__460 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe (coe d__'60''7495'__460 (coe v2) (coe v3)))
-- Once.CCC.Target.X86-64.Semantics.find-label-go
d_find'45'label'45'go_466 ::
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  Integer -> Maybe Integer
d_find'45'label'45'go_466 v0 v1 v2
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v3 v4
        -> let v5
                 = d_find'45'label'45'go_466
                     (coe v0) (coe v4) (coe addInt (coe (1 :: Integer)) (coe v2)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_64 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe
                          MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7480'__224 (coe v6)
                          (coe v0))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
                       (coe
                          d_find'45'label'45'go_466 (coe v0) (coe v4)
                          (coe addInt (coe (1 :: Integer)) (coe v2)))
                _ -> coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.find-label
d_find'45'label_484 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 -> Maybe Integer
d_find'45'label_484 v0 v1
  = coe
      d_find'45'label'45'go_466 (coe v1) (coe v0) (coe (0 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.execInstr
d_execInstr_490 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  T_State_370 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28 ->
  Maybe T_State_370
d_execInstr_490 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_30 v3 v4
        -> let v5 = d_readOperand_426 (coe v1) (coe v4) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_392 (coe d_regs_382 (coe d_writeOperand_440 v1 v3 v6))
                          (coe d_memory_384 (coe d_writeOperand_440 v1 v3 v6))
                          (coe d_flags_386 (coe d_writeOperand_440 v1 v3 v6))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_388 (coe v1)))
                          (coe d_halted_390 (coe d_writeOperand_440 v1 v3 v6)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_lea_32 v3 v4
        -> let v5
                 = coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe
                        C_mkstate_392
                        (coe
                           d_writeReg_268 (d_regs_382 (coe v1)) v3
                           (d_effectiveAddr_406 (coe v1) (coe v4)))
                        (coe d_memory_384 (coe v1)) (coe d_flags_386 (coe v1))
                        (coe addInt (coe (1 :: Integer)) (coe d_pc_388 (coe v1)))
                        (coe d_halted_390 (coe v1))) in
           coe
             (case coe v4 of
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rip'43'label_18 v6
                  -> let v7
                           = d_find'45'label_484
                               (coe v0) (coe MAlonzo.Code.Once.CCC.Label.C_thunk_28 (coe v6)) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_392 (coe d_writeReg_268 (d_regs_382 (coe v1)) v3 v8)
                                    (coe d_memory_384 (coe v1)) (coe d_flags_386 (coe v1))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_388 (coe v1)))
                                    (coe d_halted_390 (coe v1)))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_392 (coe d_regs_382 (coe v1))
                                    (coe d_memory_384 (coe v1)) (coe d_flags_386 (coe v1))
                                    (coe d_pc_388 (coe v1))
                                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v5)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_34 v3 v4
        -> let v5 = d_readOperand_426 (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> let v7 = d_readOperand_426 (coe v1) (coe v4) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_392
                                    (coe
                                       d_regs_382
                                       (coe
                                          d_writeOperand_440 v1 v3
                                          (MAlonzo.Code.Once.Word.d__'8853'__26
                                             (coe (64 :: Integer)) (coe v6) (coe v8))))
                                    (coe
                                       d_memory_384
                                       (coe
                                          d_writeOperand_440 v1 v3
                                          (MAlonzo.Code.Once.Word.d__'8853'__26
                                             (coe (64 :: Integer)) (coe v6) (coe v8))))
                                    (coe
                                       du_updateFlags_456
                                       (coe
                                          MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer))
                                          (coe v6) (coe v8)))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_388 (coe v1)))
                                    (coe
                                       d_halted_390
                                       (coe
                                          d_writeOperand_440 v1 v3
                                          (MAlonzo.Code.Once.Word.d__'8853'__26
                                             (coe (64 :: Integer)) (coe v6) (coe v8)))))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_36 v3 v4
        -> let v5 = d_readOperand_426 (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> let v7 = d_readOperand_426 (coe v1) (coe v4) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_392
                                    (coe
                                       d_regs_382
                                       (coe
                                          d_writeOperand_440 v1 v3
                                          (MAlonzo.Code.Once.Word.d__'8854'__32
                                             (coe (64 :: Integer)) (coe v6) (coe v8))))
                                    (coe
                                       d_memory_384
                                       (coe
                                          d_writeOperand_440 v1 v3
                                          (MAlonzo.Code.Once.Word.d__'8854'__32
                                             (coe (64 :: Integer)) (coe v6) (coe v8))))
                                    (coe
                                       du_updateFlags_456
                                       (coe
                                          MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
                                          (coe v6) (coe v8)))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_388 (coe v1)))
                                    (coe
                                       d_halted_390
                                       (coe
                                          d_writeOperand_440 v1 v3
                                          (MAlonzo.Code.Once.Word.d__'8854'__32
                                             (coe (64 :: Integer)) (coe v6) (coe v8)))))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_cmp_38 v3 v4
        -> let v5 = d_readOperand_426 (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> let v7 = d_readOperand_426 (coe v1) (coe v4) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_392 (coe d_regs_382 (coe v1))
                                    (coe d_memory_384 (coe v1))
                                    (coe
                                       C_mkflags_368 (coe eqInt (coe v6) (coe v8))
                                       (coe d__'60''7495'__460 (coe v6) (coe v8))
                                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_388 (coe v1)))
                                    (coe d_halted_390 (coe v1)))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_test_40 v3 v4
        -> let v5 = d_readOperand_426 (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> let v7 = d_readOperand_426 (coe v1) (coe v4) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_392 (coe d_regs_382 (coe v1))
                                    (coe d_memory_384 (coe v1))
                                    (coe
                                       C_mkflags_368 (coe eqInt (coe v6) (coe (0 :: Integer)))
                                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_388 (coe v1)))
                                    (coe d_halted_390 (coe v1)))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jmp_42 v3
        -> let v4 = d_find'45'label_484 (coe v0) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_392 (coe d_regs_382 (coe v1)) (coe d_memory_384 (coe v1))
                          (coe d_flags_386 (coe v1)) (coe v5) (coe d_halted_390 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_392 (coe d_regs_382 (coe v1)) (coe d_memory_384 (coe v1))
                          (coe d_flags_386 (coe v1)) (coe d_pc_388 (coe v1))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_je_44 v3
        -> let v4 = d_zf_362 (coe d_flags_386 (coe v1)) in
           coe
             (if coe v4
                then let v5 = d_find'45'label_484 (coe v0) (coe v3) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_392 (coe d_regs_382 (coe v1))
                                    (coe d_memory_384 (coe v1)) (coe d_flags_386 (coe v1)) (coe v6)
                                    (coe d_halted_390 (coe v1)))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_392 (coe d_regs_382 (coe v1))
                                    (coe d_memory_384 (coe v1)) (coe d_flags_386 (coe v1))
                                    (coe d_pc_388 (coe v1)) (coe v4))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                else coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_392 (coe d_regs_382 (coe v1)) (coe d_memory_384 (coe v1))
                          (coe d_flags_386 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_388 (coe v1)))
                          (coe d_halted_390 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jne_46 v3
        -> let v4 = d_zf_362 (coe d_flags_386 (coe v1)) in
           coe
             (if coe v4
                then coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_392 (coe d_regs_382 (coe v1)) (coe d_memory_384 (coe v1))
                          (coe d_flags_386 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_388 (coe v1)))
                          (coe d_halted_390 (coe v1)))
                else (let v5 = d_find'45'label_484 (coe v0) (coe v3) in
                      coe
                        (case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                  (coe
                                     C_mkstate_392 (coe d_regs_382 (coe v1))
                                     (coe d_memory_384 (coe v1)) (coe d_flags_386 (coe v1)) (coe v6)
                                     (coe d_halted_390 (coe v1)))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                  (coe
                                     C_mkstate_392 (coe d_regs_382 (coe v1))
                                     (coe d_memory_384 (coe v1)) (coe d_flags_386 (coe v1))
                                     (coe d_pc_388 (coe v1))
                                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call_48 v3
        -> let v4 = d_readOperand_426 (coe v1) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_392
                          (coe
                             d_writeReg_268 (d_regs_382 (coe v1))
                             (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_234
                                   (coe d_regs_382 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80))
                          (coe
                             d_writeMem_344 (coe d_memory_384 (coe v1))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_234
                                   (coe d_regs_382 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80)
                             (coe addInt (coe (1 :: Integer)) (coe d_pc_388 (coe v1))))
                          (coe d_flags_386 (coe v1)) (coe v5) (coe d_halted_390 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call'45'sym_50 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_392 (coe d_regs_382 (coe v1)) (coe d_memory_384 (coe v1))
                (coe d_flags_386 (coe v1)) (coe d_pc_388 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ret_52
        -> let v3
                 = d_readMem_338
                     (coe d_memory_384 (coe v1))
                     (coe
                        d_readReg_234 (coe d_regs_382 (coe v1))
                        (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_392
                          (coe
                             d_writeReg_268 (d_regs_382 (coe v1))
                             (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
                             (addInt
                                (coe
                                   d_readReg_234 (coe d_regs_382 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80)))
                          (coe d_memory_384 (coe v1)) (coe d_flags_386 (coe v1)) (coe v4)
                          (coe d_halted_390 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_push_54 v3
        -> let v4 = d_readOperand_426 (coe v1) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_392
                          (coe
                             d_writeReg_268 (d_regs_382 (coe v1))
                             (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_234
                                   (coe d_regs_382 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80))
                          (coe
                             d_writeMem_344 (coe d_memory_384 (coe v1))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_234
                                   (coe d_regs_382 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80)
                             (coe v5))
                          (coe d_flags_386 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_388 (coe v1)))
                          (coe d_halted_390 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_pop_56 v3
        -> let v4
                 = d_readMem_338
                     (coe d_memory_384 (coe v1))
                     (coe
                        d_readReg_234 (coe d_regs_382 (coe v1))
                        (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_392
                          (coe
                             d_writeReg_268 (coe d_writeReg_268 (d_regs_382 (coe v1)) v3 v5)
                             (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
                             (addInt
                                (coe
                                   d_readReg_234 (coe d_regs_382 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80)))
                          (coe d_memory_384 (coe v1)) (coe d_flags_386 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_388 (coe v1)))
                          (coe d_halted_390 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_nop_58
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_392 (coe d_regs_382 (coe v1)) (coe d_memory_384 (coe v1))
                (coe d_flags_386 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_388 (coe v1)))
                (coe d_halted_390 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_60
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_392 (coe d_regs_382 (coe v1)) (coe d_memory_384 (coe v1))
                (coe d_flags_386 (coe v1)) (coe d_pc_388 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_syscall_62
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_392 (coe d_regs_382 (coe v1)) (coe d_memory_384 (coe v1))
                (coe d_flags_386 (coe v1)) (coe d_pc_388 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_64 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_392 (coe d_regs_382 (coe v1)) (coe d_memory_384 (coe v1))
                (coe d_flags_386 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_388 (coe v1)))
                (coe d_halted_390 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.fetch
d_fetch_724 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28
d_fetch_724 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe d_fetch_724 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.step-not-halted
d_step'45'not'45'halted_732 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  T_State_370 -> Maybe T_State_370
d_step'45'not'45'halted_732 v0 v1
  = let v2 = d_fetch_724 (coe v0) (coe d_pc_388 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe d_execInstr_490 (coe v0) (coe v1) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   C_mkstate_392 (coe d_regs_382 (coe v1)) (coe d_memory_384 (coe v1))
                   (coe d_flags_386 (coe v1)) (coe d_pc_388 (coe v1))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Target.X86-64.Semantics.step
d_step_742 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  T_State_370 -> Maybe T_State_370
d_step_742 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_halted_390 (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1))
      (coe d_step'45'not'45'halted_732 (coe v0) (coe v1))
-- Once.CCC.Target.X86-64.Semantics.exec
d_exec_748 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  T_State_370 -> Maybe T_State_370
d_exec_748 v0 v1 v2
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe d_halted_390 (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
                (coe
                   d_exec'45'cont_750 (coe v3) (coe v1)
                   (coe d_step'45'not'45'halted_732 (coe v1) (coe v2))))
-- Once.CCC.Target.X86-64.Semantics.exec-cont
d_exec'45'cont_750 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  Maybe T_State_370 -> Maybe T_State_370
d_exec'45'cont_750 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_halted_390 (coe v3)) (coe v2)
             (coe d_exec_748 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.defaultFuel
d_defaultFuel_766 :: Integer
d_defaultFuel_766 = coe (10000 :: Integer)
-- Once.CCC.Target.X86-64.Semantics.run
d_run_768 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  T_State_370 -> Maybe T_State_370
d_run_768 = coe d_exec_748 (coe d_defaultFuel_766)
