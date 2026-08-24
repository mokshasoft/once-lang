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

module MAlonzo.Code.Once.CCC.Target.X86Z45Z64.CodeGen.Primitives where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW._%ˢ_
d__'37''738'__14 :: Integer -> Integer -> Integer
d__'37''738'__14
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__126 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW._/ˢ_
d__'47''738'__16 :: Integer -> Integer -> Integer
d__'47''738'__16
  = coe
      MAlonzo.Code.Once.Word.d__'47''738'__120 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW._<ˢ_
d__'60''738'__18 :: Integer -> Integer -> Bool
d__'60''738'__18
  = coe MAlonzo.Code.Once.Word.d__'60''738'__80 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW._≡ʷ_
d__'8801''695'__20 :: Integer -> Integer -> Bool
d__'8801''695'__20 = coe MAlonzo.Code.Once.Word.du__'8801''695'__86
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW._⊕_
d__'8853'__22 :: Integer -> Integer -> Integer
d__'8853'__22
  = coe MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW._⊖_
d__'8854'__24 :: Integer -> Integer -> Integer
d__'8854'__24
  = coe MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW._⊗_
d__'8855'__26 :: Integer -> Integer -> Integer
d__'8855'__26
  = coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.%ˢ-else
d_'37''738''45'else_28 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_28 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.%ˢ-in-range
d_'37''738''45'in'45'range_30 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_30 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_604
      (coe (64 :: Integer)) v2 v3 v4
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.%ˢ-mid
d_'37''738''45'mid_32 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_32 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.%ˢ-negOne
d_'37''738''45'negOne_34 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_34 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.%ˢ-zero
d_'37''738''45'zero_36 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_36 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW./ˢ-else
d_'47''738''45'else_38 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_38 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW./ˢ-in-range
d_'47''738''45'in'45'range_40 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_40 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_570
      (coe (64 :: Integer)) v2 v3
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW./ˢ-mid
d_'47''738''45'mid_42 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_42 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW./ˢ-negOne
d_'47''738''45'negOne_44 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_44 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW./ˢ-pow2
d_'47''738''45'pow2_46 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_46 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW./ˢ-zero
d_'47''738''45'zero_48 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_48 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.0<half
d_0'60'half_50 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_50 = coe MAlonzo.Code.Once.Word.du_0'60'half_168
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.0<modulus
d_0'60'modulus_52 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_52 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_166
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.0<negOne
d_0'60'negOne_54 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_54 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_426 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.1<modulus
d_1'60'modulus_56 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_56
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_796 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.2*n≡n+n
d_2'42'n'8801'n'43'n_58 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_58 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.2≤modulus
d_2'8804'modulus_60 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_60 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_422 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.<⇒<ᵇtrue
d_'60''8658''60''7495'true_62 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8658''60''7495'true_62 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.InRange
d_InRange_64 :: Integer -> ()
d_InRange_64 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.Word
d_Word_66 :: ()
d_Word_66 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.fromℤ
d_fromℤ_68 :: Integer -> Integer
d_fromℤ_68
  = coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.fromℤ-0
d_fromℤ'45'0_70 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_70 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.fromℤ-in-range
d_fromℤ'45'in'45'range_72 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_72
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_174
      (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_74 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_74 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.fromℤ-neg1
d_fromℤ'45'neg1_76 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_76 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.half
d_half_78 :: Integer
d_half_78
  = coe MAlonzo.Code.Once.Word.d_half_48 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.half<modulus
d_half'60'modulus_80 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_80 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_430 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.half≡2^b
d_half'8801'2'94'b_82 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_82 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.half≤negOne
d_half'8804'negOne_84 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_84 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_450
      (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.inRange?
d_inRange'63'_86 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_86
  = coe MAlonzo.Code.Once.Word.d_inRange'63'_62 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.intMin
d_intMin_88 :: Integer
d_intMin_88
  = coe MAlonzo.Code.Once.Word.d_intMin_54 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.lit-hi
d_lit'45'hi_90 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'hi_90 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Word.du_lit'45'hi_654 v3
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.lit-lo
d_lit'45'lo_92 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'lo_92 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_lit'45'lo_666 (coe (64 :: Integer)) v2 v3
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.modulus
d_modulus_94 :: Integer
d_modulus_94
  = coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_96 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_96 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.modulus≢0
d_modulus'8802'0_98 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_98
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.mod∸half≡half
d_mod'8760'half'8801'half_100 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_100 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.mod≡half+half
d_mod'8801'half'43'half_102 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_102 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.negOne
d_negOne_104 :: Integer
d_negOne_104
  = coe MAlonzo.Code.Once.Word.d_negOne_78 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.negOne<modulus
d_negOne'60'modulus_106 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_106 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_438
      (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.negOne≢0
d_negOne'8802'0_108 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_108 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.norm
d_norm_110 :: Integer -> Integer
d_norm_110
  = coe MAlonzo.Code.Once.Word.d_norm_16 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.norm-0
d_norm'45'0_112 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_112 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.norm-id
d_norm'45'id_114 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_114 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.sdiv2ᵏ
d_sdiv2'7503'_116 :: Integer -> Integer -> Integer
d_sdiv2'7503'_116
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_138 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.shlᵂ
d_shl'7490'_118 :: Integer -> Integer -> Integer
d_shl'7490'_118
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_132 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.sucNegOne≡mod
d_sucNegOne'8801'mod_120 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_120 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.tdiv-neg1
d_tdiv'45'neg1_122 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_122 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.tmod-neg1
d_tmod'45'neg1_124 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_124 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.toWord
d_toWord_126 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_126 v0 v1
  = coe MAlonzo.Code.Once.Word.du_toWord_68 (coe (64 :: Integer)) v0
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.toWord≡fromℤ
d_toWord'8801'fromℤ_128 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'8801'fromℤ_128 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.toℤ
d_toℤ_130 :: Integer -> Integer
d_toℤ_130
  = coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.toℤ-negOne
d_toℤ'45'negOne_132 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_132 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.toℤ∘fromℤ
d_toℤ'8728'fromℤ_134 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'8728'fromℤ_134 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.unplus
d_unplus_136 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_unplus_136 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Word.du_unplus_648 v4
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.≡ᵇ-refl
d_'8801''7495''45'refl_138 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_138 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.≡ᵇ0-false
d_'8801''7495'0'45'false_140 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_140 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_142 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_142 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.⊕-neg
d_'8853''45'neg_144 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_144 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.⊕-neg-suc
d_'8853''45'neg'45'suc_146 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_146 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.⊕-normʳ
d_'8853''45'norm'691'_148 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_148 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.⊕≡+
d_'8853''8801''43'_150 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_150 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.⊖-normʳ
d_'8854''45'norm'691'_152 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_152 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.⊖≡∸
d_'8854''8801''8760'_154 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_154 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.⊗-pow2
d_'8855''45'pow2_156 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_156 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.⊝_
d_'8861'__158 :: Integer -> Integer
d_'8861'__158
  = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.⊝-fromℤ
d_'8861''45'fromℤ_160 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'fromℤ_160 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.⊝-intMin
d_'8861''45'intMin_162 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_162 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.⊝-invol-norm
d_'8861''45'invol'45'norm_164 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'invol'45'norm_164 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.compile-sigOp
d_compile'45'sigOp_166 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28]
d_compile'45'sigOp_166 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call'45'sym_50
         (coe
            MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_52
            (coe v0)))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Target.X86-64.CodeGen.Primitives.compile-sigOp-size
d_compile'45'sigOp'45'size_170 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> Integer
d_compile'45'sigOp'45'size_170 ~v0
  = du_compile'45'sigOp'45'size_170
du_compile'45'sigOp'45'size_170 :: Integer
du_compile'45'sigOp'45'size_170 = coe (1 :: Integer)
-- Once.CCC.Target.X86-64.CodeGen.Primitives.compile-sigOp-length
d_compile'45'sigOp'45'length_174 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compile'45'sigOp'45'length_174 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.compile-const
d_compile'45'const_180 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  AgdaAny ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28]
d_compile'45'const_180 ~v0 v1 v2 = du_compile'45'const_180 v1 v2
du_compile'45'const_180 ::
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  AgdaAny ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28]
du_compile'45'const_180 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_fits'45'int_198
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_26
                   (coe
                      MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer)) (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Type.C_fits'45'float_200
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_26
                   (coe
                      MAlonzo.Code.Once.Float.Dyadic.d_encode_140
                      (coe MAlonzo.Code.Once.Float.Dyadic.d_binary64_42) (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.CodeGen.Primitives.compile-const-size
d_compile'45'const'45'size_188 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 -> Integer
d_compile'45'const'45'size_188 ~v0 v1
  = du_compile'45'const'45'size_188 v1
du_compile'45'const'45'size_188 ::
  MAlonzo.Code.Once.Type.T_FitsInReg_196 -> Integer
du_compile'45'const'45'size_188 v0
  = coe seq (coe v0) (coe (1 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.compile-const-length
d_compile'45'const'45'length_196 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compile'45'const'45'length_196 = erased
