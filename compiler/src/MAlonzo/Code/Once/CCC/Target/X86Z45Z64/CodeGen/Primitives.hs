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
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Word

-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW._%ˢ_
d__'37''738'__14 :: Integer -> Integer -> Integer
d__'37''738'__14
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__104 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW._/ˢ_
d__'47''738'__16 :: Integer -> Integer -> Integer
d__'47''738'__16
  = coe MAlonzo.Code.Once.Word.d__'47''738'__98 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW._<ˢ_
d__'60''738'__18 :: Integer -> Integer -> Bool
d__'60''738'__18
  = coe MAlonzo.Code.Once.Word.d__'60''738'__58 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW._≡ʷ_
d__'8801''695'__20 :: Integer -> Integer -> Bool
d__'8801''695'__20 = coe MAlonzo.Code.Once.Word.du__'8801''695'__64
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
      MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_526
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
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_492
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
d_0'60'half_50 = coe MAlonzo.Code.Once.Word.du_0'60'half_146
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.0<modulus
d_0'60'modulus_52 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_52 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_144
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.0<negOne
d_0'60'negOne_54 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_54 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_348 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.1<modulus
d_1'60'modulus_56 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_56
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_628 (coe (64 :: Integer))
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
      MAlonzo.Code.Once.Word.du_2'8804'modulus_344 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.Word
d_Word_62 :: ()
d_Word_62 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.fromℤ
d_fromℤ_64 :: Integer -> Integer
d_fromℤ_64
  = coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.fromℤ-0
d_fromℤ'45'0_66 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_66 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.fromℤ-in-range
d_fromℤ'45'in'45'range_68 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_68
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_152
      (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_70 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_70 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.fromℤ-neg1
d_fromℤ'45'neg1_72 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_72 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.half
d_half_74 :: Integer
d_half_74
  = coe MAlonzo.Code.Once.Word.d_half_48 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.half<modulus
d_half'60'modulus_76 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_76 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_352 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.half≡2^b
d_half'8801'2'94'b_78 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_78 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.half≤negOne
d_half'8804'negOne_80 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_80 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_372
      (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.intMin
d_intMin_82 :: Integer
d_intMin_82
  = coe MAlonzo.Code.Once.Word.d_intMin_54 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.modulus
d_modulus_84 :: Integer
d_modulus_84
  = coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_86 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_86 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.modulus≢0
d_modulus'8802'0_88 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_88
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.mod∸half≡half
d_mod'8760'half'8801'half_90 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_90 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.mod≡half+half
d_mod'8801'half'43'half_92 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_92 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.negOne
d_negOne_94 :: Integer
d_negOne_94
  = coe MAlonzo.Code.Once.Word.d_negOne_56 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.negOne<modulus
d_negOne'60'modulus_96 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_96 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_360
      (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.negOne≢0
d_negOne'8802'0_98 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_98 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.norm
d_norm_100 :: Integer -> Integer
d_norm_100
  = coe MAlonzo.Code.Once.Word.d_norm_16 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.norm-0
d_norm'45'0_102 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_102 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.norm-id
d_norm'45'id_104 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_104 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.sdiv2ᵏ
d_sdiv2'7503'_106 :: Integer -> Integer -> Integer
d_sdiv2'7503'_106
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_116 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.shlᵂ
d_shl'7490'_108 :: Integer -> Integer -> Integer
d_shl'7490'_108
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_110 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.sucNegOne≡mod
d_sucNegOne'8801'mod_110 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_110 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.tdiv-neg1
d_tdiv'45'neg1_112 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_112 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.tmod-neg1
d_tmod'45'neg1_114 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_114 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.toℤ
d_toℤ_116 :: Integer -> Integer
d_toℤ_116
  = coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.toℤ-negOne
d_toℤ'45'negOne_118 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_118 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.≡ᵇ-refl
d_'8801''7495''45'refl_120 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_120 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.≡ᵇ0-false
d_'8801''7495'0'45'false_122 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_122 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_124 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_124 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.⊕-neg
d_'8853''45'neg_126 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_126 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.⊕-neg-suc
d_'8853''45'neg'45'suc_128 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_128 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.⊕-normʳ
d_'8853''45'norm'691'_130 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_130 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.⊕≡+
d_'8853''8801''43'_132 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_132 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.⊖-normʳ
d_'8854''45'norm'691'_134 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_134 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.⊖≡∸
d_'8854''8801''8760'_136 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_136 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.⊗-pow2
d_'8855''45'pow2_138 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_138 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.⊝_
d_'8861'__140 :: Integer -> Integer
d_'8861'__140
  = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.⊝-intMin
d_'8861''45'intMin_142 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_142 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.compile-sigOp
d_compile'45'sigOp_144 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28]
d_compile'45'sigOp_144 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call'45'sym_50
         (coe
            MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_52
            (coe v0)))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Target.X86-64.CodeGen.Primitives.compile-sigOp-size
d_compile'45'sigOp'45'size_148 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> Integer
d_compile'45'sigOp'45'size_148 ~v0
  = du_compile'45'sigOp'45'size_148
du_compile'45'sigOp'45'size_148 :: Integer
du_compile'45'sigOp'45'size_148 = coe (1 :: Integer)
-- Once.CCC.Target.X86-64.CodeGen.Primitives.compile-sigOp-length
d_compile'45'sigOp'45'length_152 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compile'45'sigOp'45'length_152 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.compile-const
d_compile'45'const_158 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  AgdaAny ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28]
d_compile'45'const_158 ~v0 v1 v2 = du_compile'45'const_158 v1 v2
du_compile'45'const_158 ::
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  AgdaAny ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28]
du_compile'45'const_158 v0 v1
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
d_compile'45'const'45'size_166 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 -> Integer
d_compile'45'const'45'size_166 ~v0 v1
  = du_compile'45'const'45'size_166 v1
du_compile'45'const'45'size_166 ::
  MAlonzo.Code.Once.Type.T_FitsInReg_196 -> Integer
du_compile'45'const'45'size_166 v0
  = coe seq (coe v0) (coe (1 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.compile-const-length
d_compile'45'const'45'length_174 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compile'45'const'45'length_174 = erased
