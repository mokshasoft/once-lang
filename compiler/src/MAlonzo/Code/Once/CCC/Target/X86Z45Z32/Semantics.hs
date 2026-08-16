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
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax
import qualified MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg
import qualified MAlonzo.Code.Once.Word

-- Once.CCC.Target.X86-32.Semantics.W._%ˢ_
d__'37''738'__12 :: Integer -> Integer -> Integer
d__'37''738'__12
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__104 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W._/ˢ_
d__'47''738'__14 :: Integer -> Integer -> Integer
d__'47''738'__14
  = coe MAlonzo.Code.Once.Word.d__'47''738'__98 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W._<ˢ_
d__'60''738'__16 :: Integer -> Integer -> Bool
d__'60''738'__16
  = coe MAlonzo.Code.Once.Word.d__'60''738'__58 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W._≡ʷ_
d__'8801''695'__18 :: Integer -> Integer -> Bool
d__'8801''695'__18 = coe MAlonzo.Code.Once.Word.du__'8801''695'__64
-- Once.CCC.Target.X86-32.Semantics.W._⊕_
d__'8853'__20 :: Integer -> Integer -> Integer
d__'8853'__20
  = coe MAlonzo.Code.Once.Word.d__'8853'__26 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W._⊖_
d__'8854'__22 :: Integer -> Integer -> Integer
d__'8854'__22
  = coe MAlonzo.Code.Once.Word.d__'8854'__32 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W._⊗_
d__'8855'__24 :: Integer -> Integer -> Integer
d__'8855'__24
  = coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.%ˢ-else
d_'37''738''45'else_26 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_26 = erased
-- Once.CCC.Target.X86-32.Semantics.W.%ˢ-in-range
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
      (coe (32 :: Integer)) v2 v3 v4
-- Once.CCC.Target.X86-32.Semantics.W.%ˢ-mid
d_'37''738''45'mid_30 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_30 = erased
-- Once.CCC.Target.X86-32.Semantics.W.%ˢ-negOne
d_'37''738''45'negOne_32 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_32 = erased
-- Once.CCC.Target.X86-32.Semantics.W.%ˢ-zero
d_'37''738''45'zero_34 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_34 = erased
-- Once.CCC.Target.X86-32.Semantics.W./ˢ-else
d_'47''738''45'else_36 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_36 = erased
-- Once.CCC.Target.X86-32.Semantics.W./ˢ-in-range
d_'47''738''45'in'45'range_38 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_38 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_492
      (coe (32 :: Integer)) v2 v3
-- Once.CCC.Target.X86-32.Semantics.W./ˢ-mid
d_'47''738''45'mid_40 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_40 = erased
-- Once.CCC.Target.X86-32.Semantics.W./ˢ-negOne
d_'47''738''45'negOne_42 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_42 = erased
-- Once.CCC.Target.X86-32.Semantics.W./ˢ-pow2
d_'47''738''45'pow2_44 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_44 = erased
-- Once.CCC.Target.X86-32.Semantics.W./ˢ-zero
d_'47''738''45'zero_46 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_46 = erased
-- Once.CCC.Target.X86-32.Semantics.W.0<half
d_0'60'half_48 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_48 = coe MAlonzo.Code.Once.Word.du_0'60'half_146
-- Once.CCC.Target.X86-32.Semantics.W.0<modulus
d_0'60'modulus_50 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_50 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_144
-- Once.CCC.Target.X86-32.Semantics.W.0<negOne
d_0'60'negOne_52 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_52 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_348 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.1<modulus
d_1'60'modulus_54 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_54
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_628 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.2*n≡n+n
d_2'42'n'8801'n'43'n_56 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_56 = erased
-- Once.CCC.Target.X86-32.Semantics.W.2≤modulus
d_2'8804'modulus_58 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_58 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_344 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.Word
d_Word_60 :: ()
d_Word_60 = erased
-- Once.CCC.Target.X86-32.Semantics.W.fromℤ
d_fromℤ_62 :: Integer -> Integer
d_fromℤ_62
  = coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.fromℤ-0
d_fromℤ'45'0_64 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_64 = erased
-- Once.CCC.Target.X86-32.Semantics.W.fromℤ-in-range
d_fromℤ'45'in'45'range_66 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_66
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_152
      (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_68 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_68 = erased
-- Once.CCC.Target.X86-32.Semantics.W.fromℤ-neg1
d_fromℤ'45'neg1_70 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_70 = erased
-- Once.CCC.Target.X86-32.Semantics.W.half
d_half_72 :: Integer
d_half_72
  = coe MAlonzo.Code.Once.Word.d_half_48 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.half<modulus
d_half'60'modulus_74 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_74 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_352 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.half≡2^b
d_half'8801'2'94'b_76 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_76 = erased
-- Once.CCC.Target.X86-32.Semantics.W.half≤negOne
d_half'8804'negOne_78 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_78 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_372
      (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.intMin
d_intMin_80 :: Integer
d_intMin_80
  = coe MAlonzo.Code.Once.Word.d_intMin_54 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.modulus
d_modulus_82 :: Integer
d_modulus_82
  = coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_84 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_84 = erased
-- Once.CCC.Target.X86-32.Semantics.W.modulus≢0
d_modulus'8802'0_86 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_86
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.mod∸half≡half
d_mod'8760'half'8801'half_88 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_88 = erased
-- Once.CCC.Target.X86-32.Semantics.W.mod≡half+half
d_mod'8801'half'43'half_90 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_90 = erased
-- Once.CCC.Target.X86-32.Semantics.W.negOne
d_negOne_92 :: Integer
d_negOne_92
  = coe MAlonzo.Code.Once.Word.d_negOne_56 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.negOne<modulus
d_negOne'60'modulus_94 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_94 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_360
      (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.negOne≢0
d_negOne'8802'0_96 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_96 = erased
-- Once.CCC.Target.X86-32.Semantics.W.norm
d_norm_98 :: Integer -> Integer
d_norm_98
  = coe MAlonzo.Code.Once.Word.d_norm_16 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.norm-0
d_norm'45'0_100 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_100 = erased
-- Once.CCC.Target.X86-32.Semantics.W.norm-id
d_norm'45'id_102 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_102 = erased
-- Once.CCC.Target.X86-32.Semantics.W.sdiv2ᵏ
d_sdiv2'7503'_104 :: Integer -> Integer -> Integer
d_sdiv2'7503'_104
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_116 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.shlᵂ
d_shl'7490'_106 :: Integer -> Integer -> Integer
d_shl'7490'_106
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_110 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.sucNegOne≡mod
d_sucNegOne'8801'mod_108 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_108 = erased
-- Once.CCC.Target.X86-32.Semantics.W.tdiv-neg1
d_tdiv'45'neg1_110 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_110 = erased
-- Once.CCC.Target.X86-32.Semantics.W.tmod-neg1
d_tmod'45'neg1_112 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_112 = erased
-- Once.CCC.Target.X86-32.Semantics.W.toℤ
d_toℤ_114 :: Integer -> Integer
d_toℤ_114
  = coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.toℤ-negOne
d_toℤ'45'negOne_116 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_116 = erased
-- Once.CCC.Target.X86-32.Semantics.W.≡ᵇ-refl
d_'8801''7495''45'refl_118 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_118 = erased
-- Once.CCC.Target.X86-32.Semantics.W.≡ᵇ0-false
d_'8801''7495'0'45'false_120 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_120 = erased
-- Once.CCC.Target.X86-32.Semantics.W.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_122 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_122 = erased
-- Once.CCC.Target.X86-32.Semantics.W.⊕-neg
d_'8853''45'neg_124 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_124 = erased
-- Once.CCC.Target.X86-32.Semantics.W.⊕-neg-suc
d_'8853''45'neg'45'suc_126 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_126 = erased
-- Once.CCC.Target.X86-32.Semantics.W.⊕-normʳ
d_'8853''45'norm'691'_128 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_128 = erased
-- Once.CCC.Target.X86-32.Semantics.W.⊕≡+
d_'8853''8801''43'_130 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_130 = erased
-- Once.CCC.Target.X86-32.Semantics.W.⊖-normʳ
d_'8854''45'norm'691'_132 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_132 = erased
-- Once.CCC.Target.X86-32.Semantics.W.⊖≡∸
d_'8854''8801''8760'_134 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_134 = erased
-- Once.CCC.Target.X86-32.Semantics.W.⊗-pow2
d_'8855''45'pow2_136 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_136 = erased
-- Once.CCC.Target.X86-32.Semantics.W.⊝_
d_'8861'__138 :: Integer -> Integer
d_'8861'__138
  = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.W.⊝-intMin
d_'8861''45'intMin_140 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_140 = erased
-- Once.CCC.Target.X86-32.Semantics.Word
d_Word_142 :: ()
d_Word_142 = erased
-- Once.CCC.Target.X86-32.Semantics.RegFile
d_RegFile_144 = ()
data T_RegFile_144
  = C_mkregfile_178 Integer Integer Integer Integer Integer Integer
                    Integer Integer
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-eax
d_get'45'eax_162 :: T_RegFile_144 -> Integer
d_get'45'eax_162 v0
  = case coe v0 of
      C_mkregfile_178 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-ebx
d_get'45'ebx_164 :: T_RegFile_144 -> Integer
d_get'45'ebx_164 v0
  = case coe v0 of
      C_mkregfile_178 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-ecx
d_get'45'ecx_166 :: T_RegFile_144 -> Integer
d_get'45'ecx_166 v0
  = case coe v0 of
      C_mkregfile_178 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-edx
d_get'45'edx_168 :: T_RegFile_144 -> Integer
d_get'45'edx_168 v0
  = case coe v0 of
      C_mkregfile_178 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-esi
d_get'45'esi_170 :: T_RegFile_144 -> Integer
d_get'45'esi_170 v0
  = case coe v0 of
      C_mkregfile_178 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-edi
d_get'45'edi_172 :: T_RegFile_144 -> Integer
d_get'45'edi_172 v0
  = case coe v0 of
      C_mkregfile_178 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-ebp
d_get'45'ebp_174 :: T_RegFile_144 -> Integer
d_get'45'ebp_174 v0
  = case coe v0 of
      C_mkregfile_178 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-esp
d_get'45'esp_176 :: T_RegFile_144 -> Integer
d_get'45'esp_176 v0
  = case coe v0 of
      C_mkregfile_178 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.readReg
d_readReg_180 ::
  T_RegFile_144 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer
d_readReg_180 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10
        -> coe d_get'45'eax_162 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebx_12
        -> coe d_get'45'ebx_164 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14
        -> coe d_get'45'ecx_166 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edx_16
        -> coe d_get'45'edx_168 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esi_18
        -> coe d_get'45'esi_170 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edi_20
        -> coe d_get'45'edi_172 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebp_22
        -> coe d_get'45'ebp_174 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24
        -> coe d_get'45'esp_176 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.writeReg
d_writeReg_198 ::
  T_RegFile_144 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  Integer -> T_RegFile_144
d_writeReg_198 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_178 (coe v2) (coe d_get'45'ebx_164 (coe v0))
                  (coe d_get'45'ecx_166 (coe v0)) (coe d_get'45'edx_168 (coe v0))
                  (coe d_get'45'esi_170 (coe v0)) (coe d_get'45'edi_172 (coe v0))
                  (coe d_get'45'ebp_174 (coe v0)) (coe d_get'45'esp_176 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebx_12
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_178 (coe d_get'45'eax_162 (coe v0)) (coe v2)
                  (coe d_get'45'ecx_166 (coe v0)) (coe d_get'45'edx_168 (coe v0))
                  (coe d_get'45'esi_170 (coe v0)) (coe d_get'45'edi_172 (coe v0))
                  (coe d_get'45'ebp_174 (coe v0)) (coe d_get'45'esp_176 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_178 (coe d_get'45'eax_162 (coe v0))
                  (coe d_get'45'ebx_164 (coe v0)) (coe v2)
                  (coe d_get'45'edx_168 (coe v0)) (coe d_get'45'esi_170 (coe v0))
                  (coe d_get'45'edi_172 (coe v0)) (coe d_get'45'ebp_174 (coe v0))
                  (coe d_get'45'esp_176 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edx_16
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_178 (coe d_get'45'eax_162 (coe v0))
                  (coe d_get'45'ebx_164 (coe v0)) (coe d_get'45'ecx_166 (coe v0))
                  (coe v2) (coe d_get'45'esi_170 (coe v0))
                  (coe d_get'45'edi_172 (coe v0)) (coe d_get'45'ebp_174 (coe v0))
                  (coe d_get'45'esp_176 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esi_18
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_178 (coe d_get'45'eax_162 (coe v0))
                  (coe d_get'45'ebx_164 (coe v0)) (coe d_get'45'ecx_166 (coe v0))
                  (coe d_get'45'edx_168 (coe v0)) (coe v2)
                  (coe d_get'45'edi_172 (coe v0)) (coe d_get'45'ebp_174 (coe v0))
                  (coe d_get'45'esp_176 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edi_20
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_178 (coe d_get'45'eax_162 (coe v0))
                  (coe d_get'45'ebx_164 (coe v0)) (coe d_get'45'ecx_166 (coe v0))
                  (coe d_get'45'edx_168 (coe v0)) (coe d_get'45'esi_170 (coe v0))
                  (coe v2) (coe d_get'45'ebp_174 (coe v0))
                  (coe d_get'45'esp_176 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebp_22
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_178 (coe d_get'45'eax_162 (coe v0))
                  (coe d_get'45'ebx_164 (coe v0)) (coe d_get'45'ecx_166 (coe v0))
                  (coe d_get'45'edx_168 (coe v0)) (coe d_get'45'esi_170 (coe v0))
                  (coe d_get'45'edi_172 (coe v0)) (coe v2)
                  (coe d_get'45'esp_176 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_178 (coe d_get'45'eax_162 (coe v0))
                  (coe d_get'45'ebx_164 (coe v0)) (coe d_get'45'ecx_166 (coe v0))
                  (coe d_get'45'edx_168 (coe v0)) (coe d_get'45'esi_170 (coe v0))
                  (coe d_get'45'edi_172 (coe v0)) (coe d_get'45'ebp_174 (coe v0))
                  (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.Addr
d_Addr_232 :: ()
d_Addr_232 = erased
-- Once.CCC.Target.X86-32.Semantics.Memory
d_Memory_234 :: ()
d_Memory_234 = erased
-- Once.CCC.Target.X86-32.Semantics.readMem
d_readMem_236 ::
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
d_readMem_236 v0 v1 = coe v0 v1
-- Once.CCC.Target.X86-32.Semantics.writeMem
d_writeMem_242 ::
  (Integer -> Maybe Integer) ->
  Integer -> Integer -> Integer -> Maybe Integer
d_writeMem_242 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v3) (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
      (coe v0 v3)
-- Once.CCC.Target.X86-32.Semantics.Flags
d_Flags_252 = ()
data T_Flags_252 = C_mkflags_266 Bool Bool Bool
-- Once.CCC.Target.X86-32.Semantics.Flags.zf
d_zf_260 :: T_Flags_252 -> Bool
d_zf_260 v0
  = case coe v0 of
      C_mkflags_266 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.Flags.cf
d_cf_262 :: T_Flags_252 -> Bool
d_cf_262 v0
  = case coe v0 of
      C_mkflags_266 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.Flags.sf
d_sf_264 :: T_Flags_252 -> Bool
d_sf_264 v0
  = case coe v0 of
      C_mkflags_266 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.State
d_State_268 = ()
data T_State_268
  = C_mkstate_290 T_RegFile_144 (Integer -> Maybe Integer)
                  T_Flags_252 Integer Bool
-- Once.CCC.Target.X86-32.Semantics.State.regs
d_regs_280 :: T_State_268 -> T_RegFile_144
d_regs_280 v0
  = case coe v0 of
      C_mkstate_290 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.State.memory
d_memory_282 :: T_State_268 -> Integer -> Maybe Integer
d_memory_282 v0
  = case coe v0 of
      C_mkstate_290 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.State.flags
d_flags_284 :: T_State_268 -> T_Flags_252
d_flags_284 v0
  = case coe v0 of
      C_mkstate_290 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.State.pc
d_pc_286 :: T_State_268 -> Integer
d_pc_286 v0
  = case coe v0 of
      C_mkstate_290 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.State.halted
d_halted_288 :: T_State_268 -> Bool
d_halted_288 v0
  = case coe v0 of
      C_mkstate_290 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.emptyRegFile
d_emptyRegFile_292 :: T_RegFile_144
d_emptyRegFile_292
  = coe
      C_mkregfile_178 (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.emptyMemory
d_emptyMemory_294 :: Integer -> Maybe Integer
d_emptyMemory_294 ~v0 = du_emptyMemory_294
du_emptyMemory_294 :: Maybe Integer
du_emptyMemory_294
  = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.CCC.Target.X86-32.Semantics.initFlags
d_initFlags_298 :: T_Flags_252
d_initFlags_298
  = coe
      C_mkflags_266 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.CCC.Target.X86-32.Semantics.initState
d_initState_300 :: T_State_268
d_initState_300
  = coe
      C_mkstate_290 (coe d_emptyRegFile_292)
      (\ v0 -> coe du_emptyMemory_294) (coe d_initFlags_298)
      (coe (0 :: Integer)) (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.CCC.Target.X86-32.Semantics.effectiveAddr
d_effectiveAddr_302 ::
  T_State_268 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Mem_10 -> Integer
d_effectiveAddr_302 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base_12 v2
        -> coe d_readReg_180 (coe d_regs_280 (coe v0)) (coe v2)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14 v2 v3
        -> coe
             addInt (coe d_readReg_180 (coe d_regs_280 (coe v0)) (coe v2))
             (coe v3)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label'45'rel_16 v2
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.readOperand
d_readOperand_318 ::
  T_State_268 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Operand_18 ->
  Maybe Integer
d_readOperand_318 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe d_readReg_180 (coe d_regs_280 (coe v0)) (coe v2))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_22 v2
        -> coe
             d_readMem_236 (coe d_memory_282 (coe v0))
             (coe d_effectiveAddr_302 (coe v0) (coe v2))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_24 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.Word.d_norm_16 (coe (32 :: Integer)) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.writeOperand
d_writeOperand_332 ::
  T_State_268 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Operand_18 ->
  Integer -> T_State_268
d_writeOperand_332 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkstate_290 (coe d_writeReg_198 (d_regs_280 (coe v0)) v2 v3)
                  (coe d_memory_282 (coe v0)) (coe d_flags_284 (coe v0))
                  (coe d_pc_286 (coe v0)) (coe d_halted_288 (coe v0)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_22 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkstate_290 (coe d_regs_280 (coe v0))
                  (coe
                     d_writeMem_242 (coe d_memory_282 (coe v0))
                     (coe d_effectiveAddr_302 (coe v0) (coe v2)) (coe v3))
                  (coe d_flags_284 (coe v0)) (coe d_pc_286 (coe v0))
                  (coe d_halted_288 (coe v0)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_24 v2
        -> coe (\ v3 -> v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.updateFlags
d_updateFlags_348 :: Integer -> T_Flags_252
d_updateFlags_348 v0
  = coe
      C_mkflags_266 (coe eqInt (coe v0) (coe (0 :: Integer)))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.CCC.Target.X86-32.Semantics._<ᵇ_
d__'60''7495'__352 :: Integer -> Integer -> Bool
d__'60''7495'__352 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe (coe d__'60''7495'__352 (coe v2) (coe v3)))
-- Once.CCC.Target.X86-32.Semantics.find-label-go
d_find'45'label'45'go_358 ::
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  Integer -> Maybe Integer
d_find'45'label'45'go_358 v0 v1 v2
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v3 v4
        -> let v5
                 = d_find'45'label'45'go_358
                     (coe v0) (coe v4) (coe addInt (coe (1 :: Integer)) (coe v2)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label_60 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe
                          MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7480'__224 (coe v6)
                          (coe v0))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
                       (coe
                          d_find'45'label'45'go_358 (coe v0) (coe v4)
                          (coe addInt (coe (1 :: Integer)) (coe v2)))
                _ -> coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.find-label
d_find'45'label_376 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 -> Maybe Integer
d_find'45'label_376 v0 v1
  = coe
      d_find'45'label'45'go_358 (coe v1) (coe v0) (coe (0 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.execInstr
d_execInstr_382 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  T_State_268 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26 ->
  Maybe T_State_268
d_execInstr_382 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28 v3 v4
        -> let v5 = d_readOperand_318 (coe v1) (coe v4) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_290 (coe d_regs_280 (coe d_writeOperand_332 v1 v3 v6))
                          (coe d_memory_282 (coe d_writeOperand_332 v1 v3 v6))
                          (coe d_flags_284 (coe d_writeOperand_332 v1 v3 v6))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_286 (coe v1)))
                          (coe d_halted_288 (coe d_writeOperand_332 v1 v3 v6)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_lea_30 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_290
                (coe
                   d_writeReg_198 (d_regs_280 (coe v1)) v3
                   (d_effectiveAddr_302 (coe v1) (coe v4)))
                (coe d_memory_282 (coe v1)) (coe d_flags_284 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_286 (coe v1)))
                (coe d_halted_288 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_push_32 v3
        -> let v4 = d_readOperand_318 (coe v1) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_290
                          (coe
                             d_writeReg_198 (d_regs_280 (coe v1))
                             (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_180
                                   (coe d_regs_280 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_68))
                          (coe
                             d_writeMem_242 (coe d_memory_282 (coe v1))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_180
                                   (coe d_regs_280 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_68)
                             (coe v5))
                          (coe d_flags_284 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_286 (coe v1)))
                          (coe d_halted_288 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_pop_34 v3
        -> let v4
                 = d_readMem_236
                     (coe d_memory_282 (coe v1))
                     (coe
                        d_readReg_180 (coe d_regs_280 (coe v1))
                        (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_290
                          (coe
                             d_writeReg_198 (coe d_writeReg_198 (d_regs_280 (coe v1)) v3 v5)
                             (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)
                             (addInt
                                (coe
                                   d_readReg_180 (coe d_regs_280 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_68)))
                          (coe d_memory_282 (coe v1)) (coe d_flags_284 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_286 (coe v1)))
                          (coe d_halted_288 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_add_36 v3 v4
        -> let v5 = d_readOperand_318 (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> let v7 = d_readOperand_318 (coe v1) (coe v4) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_290
                                    (coe
                                       d_regs_280
                                       (coe
                                          d_writeOperand_332 v1 v3
                                          (MAlonzo.Code.Once.Word.d__'8853'__26
                                             (coe (32 :: Integer)) (coe v6) (coe v8))))
                                    (coe
                                       d_memory_282
                                       (coe
                                          d_writeOperand_332 v1 v3
                                          (MAlonzo.Code.Once.Word.d__'8853'__26
                                             (coe (32 :: Integer)) (coe v6) (coe v8))))
                                    (coe
                                       d_updateFlags_348
                                       (coe
                                          MAlonzo.Code.Once.Word.d__'8853'__26 (coe (32 :: Integer))
                                          (coe v6) (coe v8)))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_286 (coe v1)))
                                    (coe
                                       d_halted_288
                                       (coe
                                          d_writeOperand_332 v1 v3
                                          (MAlonzo.Code.Once.Word.d__'8853'__26
                                             (coe (32 :: Integer)) (coe v6) (coe v8)))))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_sub_38 v3 v4
        -> let v5 = d_readOperand_318 (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> let v7 = d_readOperand_318 (coe v1) (coe v4) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_290
                                    (coe
                                       d_regs_280
                                       (coe
                                          d_writeOperand_332 v1 v3
                                          (MAlonzo.Code.Once.Word.d__'8854'__32
                                             (coe (32 :: Integer)) (coe v6) (coe v8))))
                                    (coe
                                       d_memory_282
                                       (coe
                                          d_writeOperand_332 v1 v3
                                          (MAlonzo.Code.Once.Word.d__'8854'__32
                                             (coe (32 :: Integer)) (coe v6) (coe v8))))
                                    (coe
                                       d_updateFlags_348
                                       (coe
                                          MAlonzo.Code.Once.Word.d__'8854'__32 (coe (32 :: Integer))
                                          (coe v6) (coe v8)))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_286 (coe v1)))
                                    (coe
                                       d_halted_288
                                       (coe
                                          d_writeOperand_332 v1 v3
                                          (MAlonzo.Code.Once.Word.d__'8854'__32
                                             (coe (32 :: Integer)) (coe v6) (coe v8)))))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_cmp_40 v3 v4
        -> let v5 = d_readOperand_318 (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> let v7 = d_readOperand_318 (coe v1) (coe v4) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_290 (coe d_regs_280 (coe v1))
                                    (coe d_memory_282 (coe v1))
                                    (coe
                                       C_mkflags_266 (coe eqInt (coe v6) (coe v8))
                                       (coe d__'60''7495'__352 (coe v6) (coe v8))
                                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_286 (coe v1)))
                                    (coe d_halted_288 (coe v1)))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_test_42 v3 v4
        -> let v5 = d_readOperand_318 (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> let v7 = d_readOperand_318 (coe v1) (coe v4) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_290 (coe d_regs_280 (coe v1))
                                    (coe d_memory_282 (coe v1))
                                    (coe
                                       C_mkflags_266 (coe eqInt (coe v6) (coe (0 :: Integer)))
                                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_286 (coe v1)))
                                    (coe d_halted_288 (coe v1)))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jmp_44 v3
        -> let v4 = d_readOperand_318 (coe v1) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_290 (coe d_regs_280 (coe v1)) (coe d_memory_282 (coe v1))
                          (coe d_flags_284 (coe v1)) (coe v5) (coe d_halted_288 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jne_46 v3
        -> let v4 = d_zf_260 (coe d_flags_284 (coe v1)) in
           coe
             (if coe v4
                then coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_290 (coe d_regs_280 (coe v1)) (coe d_memory_282 (coe v1))
                          (coe d_flags_284 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_286 (coe v1)))
                          (coe d_halted_288 (coe v1)))
                else (let v5 = d_find'45'label_376 (coe v0) (coe v3) in
                      coe
                        (case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                  (coe
                                     C_mkstate_290 (coe d_regs_280 (coe v1))
                                     (coe d_memory_282 (coe v1)) (coe d_flags_284 (coe v1)) (coe v6)
                                     (coe d_halted_288 (coe v1)))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                  (coe
                                     C_mkstate_290 (coe d_regs_280 (coe v1))
                                     (coe d_memory_282 (coe v1)) (coe d_flags_284 (coe v1))
                                     (coe d_pc_286 (coe v1))
                                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_je_48 v3
        -> let v4 = d_zf_260 (coe d_flags_284 (coe v1)) in
           coe
             (if coe v4
                then let v5 = d_find'45'label_376 (coe v0) (coe v3) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_290 (coe d_regs_280 (coe v1))
                                    (coe d_memory_282 (coe v1)) (coe d_flags_284 (coe v1)) (coe v6)
                                    (coe d_halted_288 (coe v1)))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_290 (coe d_regs_280 (coe v1))
                                    (coe d_memory_282 (coe v1)) (coe d_flags_284 (coe v1))
                                    (coe d_pc_286 (coe v1)) (coe v4))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                else coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_290 (coe d_regs_280 (coe v1)) (coe d_memory_282 (coe v1))
                          (coe d_flags_284 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_286 (coe v1)))
                          (coe d_halted_288 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call_50 v3
        -> let v4 = d_readOperand_318 (coe v1) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_290
                          (coe
                             d_writeReg_198 (d_regs_280 (coe v1))
                             (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_180
                                   (coe d_regs_280 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_68))
                          (coe
                             d_writeMem_242 (coe d_memory_282 (coe v1))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_180
                                   (coe d_regs_280 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_68)
                             (coe addInt (coe (1 :: Integer)) (coe d_pc_286 (coe v1))))
                          (coe d_flags_284 (coe v1)) (coe v5) (coe d_halted_288 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call'45'sym_52 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_290 (coe d_regs_280 (coe v1)) (coe d_memory_282 (coe v1))
                (coe d_flags_284 (coe v1)) (coe d_pc_286 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ret_54
        -> let v3
                 = d_readMem_236
                     (coe d_memory_282 (coe v1))
                     (coe
                        d_readReg_180 (coe d_regs_280 (coe v1))
                        (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_290
                          (coe
                             d_writeReg_198 (d_regs_280 (coe v1))
                             (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)
                             (addInt
                                (coe
                                   d_readReg_180 (coe d_regs_280 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_68)))
                          (coe d_memory_282 (coe v1)) (coe d_flags_284 (coe v1)) (coe v4)
                          (coe d_halted_288 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_nop_56
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_290 (coe d_regs_280 (coe v1)) (coe d_memory_282 (coe v1))
                (coe d_flags_284 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_286 (coe v1)))
                (coe d_halted_288 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ud2_58
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_290 (coe d_regs_280 (coe v1)) (coe d_memory_282 (coe v1))
                (coe d_flags_284 (coe v1)) (coe d_pc_286 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label_60 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_290 (coe d_regs_280 (coe v1)) (coe d_memory_282 (coe v1))
                (coe d_flags_284 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_286 (coe v1)))
                (coe d_halted_288 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov'45'code_62 v3 v4
        -> let v5
                 = d_find'45'label_376
                     (coe v0) (coe MAlonzo.Code.Once.CCC.Label.C_thunk_28 (coe v4)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_290 (coe d_writeReg_198 (d_regs_280 (coe v1)) v3 v6)
                          (coe d_memory_282 (coe v1)) (coe d_flags_284 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_286 (coe v1)))
                          (coe d_halted_288 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_290 (coe d_regs_280 (coe v1)) (coe d_memory_282 (coe v1))
                          (coe d_flags_284 (coe v1)) (coe d_pc_286 (coe v1))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jmp'45'l_64 v3
        -> let v4 = d_find'45'label_376 (coe v0) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_290 (coe d_regs_280 (coe v1)) (coe d_memory_282 (coe v1))
                          (coe d_flags_284 (coe v1)) (coe v5) (coe d_halted_288 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_290 (coe d_regs_280 (coe v1)) (coe d_memory_282 (coe v1))
                          (coe d_flags_284 (coe v1)) (coe d_pc_286 (coe v1))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.fetch
d_fetch_622 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26
d_fetch_622 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe d_fetch_622 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.step-not-halted
d_step'45'not'45'halted_630 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  T_State_268 -> Maybe T_State_268
d_step'45'not'45'halted_630 v0 v1
  = let v2 = d_fetch_622 (coe v0) (coe d_pc_286 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe d_execInstr_382 (coe v0) (coe v1) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   C_mkstate_290 (coe d_regs_280 (coe v1)) (coe d_memory_282 (coe v1))
                   (coe d_flags_284 (coe v1)) (coe d_pc_286 (coe v1))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Target.X86-32.Semantics.step
d_step_640 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  T_State_268 -> Maybe T_State_268
d_step_640 v0 v1
  = let v2 = d_halted_288 (coe v1) in
    coe
      (if coe v2
         then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
         else coe d_step'45'not'45'halted_630 (coe v0) (coe v1))
-- Once.CCC.Target.X86-32.Semantics.exec
d_exec_658 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  T_State_268 -> Maybe T_State_268
d_exec_658 v0 v1 v2
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (let v4 = d_halted_288 (coe v2) in
              coe
                (if coe v4
                   then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                   else (let v5 = d_step'45'not'45'halted_630 (coe v1) (coe v2) in
                         coe
                           (case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                -> let v7 = d_halted_288 (coe v6) in
                                   coe
                                     (if coe v7
                                        then coe v5
                                        else coe d_exec_658 (coe v3) (coe v1) (coe v6))
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Target.X86-32.Semantics.defaultFuel
d_defaultFuel_722 :: Integer
d_defaultFuel_722 = coe (10000 :: Integer)
-- Once.CCC.Target.X86-32.Semantics.run
d_run_724 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  T_State_268 -> Maybe T_State_268
d_run_724 = coe d_exec_658 (coe d_defaultFuel_722)
