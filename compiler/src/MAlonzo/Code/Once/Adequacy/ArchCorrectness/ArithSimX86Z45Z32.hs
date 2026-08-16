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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimX86Z45Z32 where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoad
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.ExecArith
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.Arith.Machine.AbsState
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics
import qualified MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg
import qualified MAlonzo.Code.Once.Word

-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W._%ˢ_
d__'37''738'__10 :: Integer -> Integer -> Integer
d__'37''738'__10
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__104 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W._/ˢ_
d__'47''738'__12 :: Integer -> Integer -> Integer
d__'47''738'__12
  = coe MAlonzo.Code.Once.Word.d__'47''738'__98 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W._<ˢ_
d__'60''738'__14 :: Integer -> Integer -> Bool
d__'60''738'__14
  = coe MAlonzo.Code.Once.Word.d__'60''738'__58 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W._≡ʷ_
d__'8801''695'__16 :: Integer -> Integer -> Bool
d__'8801''695'__16 = coe MAlonzo.Code.Once.Word.du__'8801''695'__64
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W._⊕_
d__'8853'__18 :: Integer -> Integer -> Integer
d__'8853'__18
  = coe MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W._⊖_
d__'8854'__20 :: Integer -> Integer -> Integer
d__'8854'__20
  = coe MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W._⊗_
d__'8855'__22 :: Integer -> Integer -> Integer
d__'8855'__22
  = coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.%ˢ-else
d_'37''738''45'else_24 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_24 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.%ˢ-in-range
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
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.%ˢ-mid
d_'37''738''45'mid_28 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_28 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.%ˢ-negOne
d_'37''738''45'negOne_30 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_30 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.%ˢ-zero
d_'37''738''45'zero_32 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_32 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W./ˢ-else
d_'47''738''45'else_34 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_34 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W./ˢ-in-range
d_'47''738''45'in'45'range_36 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_36 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_492
      (coe (64 :: Integer)) v2 v3
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W./ˢ-mid
d_'47''738''45'mid_38 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_38 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W./ˢ-negOne
d_'47''738''45'negOne_40 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_40 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W./ˢ-pow2
d_'47''738''45'pow2_42 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_42 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W./ˢ-zero
d_'47''738''45'zero_44 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_44 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.0<half
d_0'60'half_46 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_46 = coe MAlonzo.Code.Once.Word.du_0'60'half_146
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.0<modulus
d_0'60'modulus_48 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_48 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_144
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.0<negOne
d_0'60'negOne_50 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_50 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_348 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.1<modulus
d_1'60'modulus_52 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_52
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_628 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.2*n≡n+n
d_2'42'n'8801'n'43'n_54 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_54 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.2≤modulus
d_2'8804'modulus_56 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_56 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_344 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.Word
d_Word_58 :: ()
d_Word_58 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.fromℤ
d_fromℤ_60 :: Integer -> Integer
d_fromℤ_60
  = coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.fromℤ-0
d_fromℤ'45'0_62 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_62 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.fromℤ-in-range
d_fromℤ'45'in'45'range_64 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_64
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_152
      (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_66 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_66 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.fromℤ-neg1
d_fromℤ'45'neg1_68 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_68 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.half
d_half_70 :: Integer
d_half_70
  = coe MAlonzo.Code.Once.Word.d_half_48 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.half<modulus
d_half'60'modulus_72 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_72 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_352 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.half≡2^b
d_half'8801'2'94'b_74 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_74 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.half≤negOne
d_half'8804'negOne_76 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_76 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_372
      (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.intMin
d_intMin_78 :: Integer
d_intMin_78
  = coe MAlonzo.Code.Once.Word.d_intMin_54 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.modulus
d_modulus_80 :: Integer
d_modulus_80
  = coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_82 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_82 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.modulus≢0
d_modulus'8802'0_84 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_84
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.mod∸half≡half
d_mod'8760'half'8801'half_86 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_86 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.mod≡half+half
d_mod'8801'half'43'half_88 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_88 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.negOne
d_negOne_90 :: Integer
d_negOne_90
  = coe MAlonzo.Code.Once.Word.d_negOne_56 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.negOne<modulus
d_negOne'60'modulus_92 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_92 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_360
      (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.negOne≢0
d_negOne'8802'0_94 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_94 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.norm
d_norm_96 :: Integer -> Integer
d_norm_96
  = coe MAlonzo.Code.Once.Word.d_norm_16 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.norm-0
d_norm'45'0_98 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_98 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.norm-id
d_norm'45'id_100 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_100 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.sdiv2ᵏ
d_sdiv2'7503'_102 :: Integer -> Integer -> Integer
d_sdiv2'7503'_102
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_116 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.shlᵂ
d_shl'7490'_104 :: Integer -> Integer -> Integer
d_shl'7490'_104
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_110 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.sucNegOne≡mod
d_sucNegOne'8801'mod_106 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_106 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.tdiv-neg1
d_tdiv'45'neg1_108 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_108 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.tmod-neg1
d_tmod'45'neg1_110 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_110 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.toℤ
d_toℤ_112 :: Integer -> Integer
d_toℤ_112
  = coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.toℤ-negOne
d_toℤ'45'negOne_114 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_114 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.≡ᵇ-refl
d_'8801''7495''45'refl_116 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_116 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.≡ᵇ0-false
d_'8801''7495'0'45'false_118 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_118 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_120 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_120 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊕-neg
d_'8853''45'neg_122 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_122 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊕-neg-suc
d_'8853''45'neg'45'suc_124 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_124 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊕-normʳ
d_'8853''45'norm'691'_126 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_126 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊕≡+
d_'8853''8801''43'_128 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_128 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊖-normʳ
d_'8854''45'norm'691'_130 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_130 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊖≡∸
d_'8854''8801''8760'_132 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_132 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊗-pow2
d_'8855''45'pow2_134 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_134 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊝_
d_'8861'__136 :: Integer -> Integer
d_'8861'__136
  = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊝-intMin
d_'8861''45'intMin_138 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_138 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.rd
d_rd_140 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 -> Integer
d_rd_140 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_readReg_180
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_regs_280
         (coe v0))
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit.d_arith'45'reg_10
         (coe v1))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.def
d_def_146 :: Maybe Integer -> Integer
d_def_146 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.scratch-addr
d_scratch'45'addr_150 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer
d_scratch'45'addr_150 v0 v1
  = coe
      addInt
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_readReg_180
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_regs_280
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
      (coe
         mulInt (coe (4 :: Integer))
         (coe
            MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.d_slot_20 (coe v1)))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.side-off
d_side'45'off_156 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22 -> Integer
d_side'45'off_156 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_24
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_26
        -> coe (4 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.path-load-go
d_path'45'load'45'go_160 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer
d_path'45'load'45'go_160
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoad.du_path'45'load'45'go_16
      (coe
         (\ v0 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_memory_282
              (coe v0)))
      (coe d_def_146) (coe d_side'45'off_156)
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.plg-mem-cong
d_plg'45'mem'45'cong_162 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_plg'45'mem'45'cong_162 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.path-load
d_path'45'load_164 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer
d_path'45'load_164 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoad.du_path'45'load'45'go_16
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_memory_282
              (coe v2)))
      (coe d_def_146) (coe d_side'45'off_156) (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_readReg_180
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_regs_280
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14))
      (coe v1)
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.val-x86-32
d_val'45'x86'45'32_170 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer
d_val'45'x86'45'32_170 v0 v1 ~v2 = du_val'45'x86'45'32_170 v0 v1
du_val'45'x86'45'32_170 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  Integer
du_val'45'x86'45'32_170 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'imm_26 v2 v3
        -> coe
             MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer)) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_28 v2 v3
        -> coe d_rd_140 (coe v1) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'r'45'm_30 v2 v3
        -> coe d_rd_140 (coe v1) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'm'45'r_32 v2 v3
        -> coe
             d_def_146
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_readMem_236
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_memory_282
                   (coe v1))
                (coe d_scratch'45'addr_150 (coe v1) (coe v3)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'arg_34 v2 v3
        -> coe d_path'45'load_164 (coe v1) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xadd'45'rr_36 v2 v3
        -> coe
             MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer))
             (coe d_rd_140 (coe v1) (coe v2)) (coe d_rd_140 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsub'45'rr_38 v2 v3
        -> coe
             MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
             (coe d_rd_140 (coe v1) (coe v2)) (coe d_rd_140 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Ximul'45'rr_40 v2 v3
        -> coe
             MAlonzo.Code.Once.Word.d__'8855'__38 (coe (64 :: Integer))
             (coe d_rd_140 (coe v1) (coe v2)) (coe d_rd_140 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xneg'45'r_42 v2
        -> coe
             MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
             (coe d_rd_140 (coe v1) (coe v2))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'rrr_44 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'47''738'__98 (coe (64 :: Integer))
             (coe d_rd_140 (coe v1) (coe v3)) (coe d_rd_140 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'rrr_46 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'37''738'__104 (coe (64 :: Integer))
             (coe d_rd_140 (coe v1) (coe v3)) (coe d_rd_140 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'safe'45'rrr_48 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'47''738'__98 (coe (64 :: Integer))
             (coe d_rd_140 (coe v1) (coe v3)) (coe d_rd_140 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'safe'45'rrr_50 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'37''738'__104 (coe (64 :: Integer))
             (coe d_rd_140 (coe v1) (coe v3)) (coe d_rd_140 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xshl'45'rri_52 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d_shl'7490'_110 (coe (64 :: Integer))
             (coe d_rd_140 (coe v1) (coe v3)) (coe v4)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsdiv'45'pow2'45'rri_54 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d_sdiv2'7503'_116 (coe (64 :: Integer))
             (coe d_rd_140 (coe v1) (coe v3)) (coe v4)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'out_56 v2
        -> coe d_rd_140 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.readReg-wr-arith-other
d_readReg'45'wr'45'arith'45'other_284 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_144 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readReg'45'wr'45'arith'45'other_284 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.readReg-wr-arith-same
d_readReg'45'wr'45'arith'45'same_312 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_144 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readReg'45'wr'45'arith'45'same_312 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.readReg-wr-eax-arith
d_readReg'45'wr'45'eax'45'arith_328 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_144 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readReg'45'wr'45'eax'45'arith_328 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.readReg-wr-eax-same
d_readReg'45'wr'45'eax'45'same_342 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_144 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readReg'45'wr'45'eax'45'same_342 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.wr-arith-esp
d_wr'45'arith'45'esp_354 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_144 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wr'45'arith'45'esp_354 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.wr-eax-esp
d_wr'45'eax'45'esp_368 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_144 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wr'45'eax'45'esp_368 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.wr-arith-ecx
d_wr'45'arith'45'ecx_380 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_144 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wr'45'arith'45'ecx_380 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.wr-eax-ecx
d_wr'45'eax'45'ecx_394 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_144 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wr'45'eax'45'ecx_394 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.rr
d_rr_400 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer
d_rr_400 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_readReg_180
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_regs_280
         (coe v0))
      (coe v1)
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.mem
d_mem_406 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  Integer -> Maybe Integer
d_mem_406 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_readMem_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_memory_282
         (coe v0))
      (coe v1)
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.V
d_V_412 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  Integer
d_V_412 v0 v1 = coe du_val'45'x86'45'32_170 (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.rf-other
d_rf'45'other_426 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rf'45'other_426 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.readMem-writeMem-same
d_readMem'45'writeMem'45'same_602 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readMem'45'writeMem'45'same_602 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.readMem-writeMem-other
d_readMem'45'writeMem'45'other_636 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readMem'45'writeMem'45'other_636 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.sa-inj
d_sa'45'inj_684 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_sa'45'inj_684 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.safe-inv
d_safe'45'inv_708 ::
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  (MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_144 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_144 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_safe'45'inv_708 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.sa-inv
d_sa'45'inv_916 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sa'45'inv_916 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.mem-keep
d_mem'45'keep_932 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'keep_932 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.mem-spill-hit
d_mem'45'spill'45'hit_1000 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'spill'45'hit_1000 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.mem-spill-miss
d_mem'45'spill'45'miss_1016 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'spill'45'miss_1016 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.pl-inv-ns
d_pl'45'inv'45'ns_1034 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pl'45'inv'45'ns_1034 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.HeapChase
d_HeapChase_1048 a0 a1 a2 = ()
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.heapchase-agree
d_heapchase'45'agree_1050 ::
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.T_HeapChase_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.T_HeapChase_42
d_heapchase'45'agree_1050 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.du_heapchase'45'agree_112
      v3 v5
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.plg
d_plg_1052 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer
d_plg_1052
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.du_plg_26
      (coe d_def_146) (coe d_side'45'off_156)
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.plg-stack-write-invisible
d_plg'45'stack'45'write'45'invisible_1054 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.T_HeapChase_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_plg'45'stack'45'write'45'invisible_1054 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.WF
d_WF_1062 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 -> ()
d_WF_1062 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.pathloadgo≡plg
d_pathloadgo'8801'plg_1076 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pathloadgo'8801'plg_1076 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.mem-agree-heap
d_mem'45'agree'45'heap_1098 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'agree'45'heap_1098 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.wf-e1
d_wf'45'e1_1304 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'e1_1304 ~v0 ~v1 v2 = du_wf'45'e1_1304 v2
du_wf'45'e1_1304 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf'45'e1_1304 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe (\ v3 -> coe v1 v3))
             (coe
                (\ v3 ->
                   coe
                     MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.du_heapchase'45'agree_112
                     (coe v3) (coe v2 v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.pl-inv
d_pl'45'inv_1326 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pl'45'inv_1326 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R
d_R_1608 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 -> ()
d_R_1608 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R-init
d_R'45'init_1610 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'init_1610 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R-input
d_R'45'input_1612 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 -> ()
d_R'45'input_1612 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R-scratch
d_R'45'scratch_1614 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 -> ()
d_R'45'scratch_1614 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R-scratch-init
d_R'45'scratch'45'init_1616 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'scratch'45'init_1616 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R-step-arg
d_R'45'step'45'arg_1618 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'step'45'arg_1618 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R-step-full
d_R'45'step'45'full_1620 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'step'45'full_1620 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R-step-reload
d_R'45'step'45'reload_1622 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'step'45'reload_1622 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Rf
d_Rf_1624 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 -> ()
d_Rf_1624 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Rf-init
d_Rf'45'init_1626 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'init_1626 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore.du_Rf'45'init_2104
      v3 v4
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Rf-sim
d_Rf'45'sim_1628 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'sim_1628 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore.du_Rf'45'sim_2054
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.ExecArith.d_exec1_82
         (\ v5 v6 v7 -> coe du_val'45'x86'45'32_170 v5 v6))
      (\ v5 v6 v7 -> coe du_wf'45'e1_1304 v7) v1 v3 v4
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Rf-step
d_Rf'45'step_1630 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'step_1630 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore.du_Rf'45'step_2028
      (\ v5 v6 v7 -> coe du_wf'45'e1_1304 v7) v1 v3 v4
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.arith-block-correct
d_arith'45'block'45'correct_1632 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arith'45'block'45'correct_1632 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.bin-value
d_bin'45'value_1634 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  Integer ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bin'45'value_1634 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.eb-++
d_eb'45''43''43'_1636 ::
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eb'45''43''43'_1636 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.frame-hyp
d_frame'45'hyp_1638 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_frame'45'hyp_1638 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.input-frame
d_input'45'frame_1640 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45'frame_1640 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.no-tgt-hyp
d_no'45'tgt'45'hyp_1642 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'tgt'45'hyp_1642 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.nonspill-sf
d_nonspill'45'sf_1644 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nonspill'45'sf_1644 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.n≢j
d_n'8802'j_1646 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8802'j_1646 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.output-extract
d_output'45'extract_1648 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_output'45'extract_1648 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.result-correct
d_result'45'correct_1650 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  Integer ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result'45'correct_1650 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.sa-slot-eq
d_sa'45'slot'45'eq_1652 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sa'45'slot'45'eq_1652 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.scratch-frame
d_scratch'45'frame_1654 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45'frame_1654 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.step-other
d_step'45'other_1656 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Maybe Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'other_1656 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.un-value
d_un'45'value_1658 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  Integer ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_un'45'value_1658 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.xreg-idx-inj
d_xreg'45'idx'45'inj_1660 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xreg'45'idx'45'inj_1660 = erased
