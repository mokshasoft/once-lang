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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimRiscV64 where

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
import qualified MAlonzo.Code.Once.Arith.Backend.RiscV64.Emit
import qualified MAlonzo.Code.Once.Arith.Backend.RiscV64.ExecArith
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.Arith.Machine.AbsState
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics
import qualified MAlonzo.Code.Once.Target.RiscV64.PhysReg
import qualified MAlonzo.Code.Once.Word

-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W._%ˢ_
d__'37''738'__10 :: Integer -> Integer -> Integer
d__'37''738'__10
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__104 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W._/ˢ_
d__'47''738'__12 :: Integer -> Integer -> Integer
d__'47''738'__12
  = coe MAlonzo.Code.Once.Word.d__'47''738'__98 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W._<ˢ_
d__'60''738'__14 :: Integer -> Integer -> Bool
d__'60''738'__14
  = coe MAlonzo.Code.Once.Word.d__'60''738'__58 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W._≡ʷ_
d__'8801''695'__16 :: Integer -> Integer -> Bool
d__'8801''695'__16 = coe MAlonzo.Code.Once.Word.du__'8801''695'__64
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W._⊕_
d__'8853'__18 :: Integer -> Integer -> Integer
d__'8853'__18
  = coe MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W._⊖_
d__'8854'__20 :: Integer -> Integer -> Integer
d__'8854'__20
  = coe MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W._⊗_
d__'8855'__22 :: Integer -> Integer -> Integer
d__'8855'__22
  = coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.%ˢ-else
d_'37''738''45'else_24 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_24 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.%ˢ-in-range
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
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.%ˢ-mid
d_'37''738''45'mid_28 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_28 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.%ˢ-negOne
d_'37''738''45'negOne_30 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_30 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.%ˢ-zero
d_'37''738''45'zero_32 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_32 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W./ˢ-else
d_'47''738''45'else_34 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_34 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W./ˢ-in-range
d_'47''738''45'in'45'range_36 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_36 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_492
      (coe (64 :: Integer)) v2 v3
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W./ˢ-mid
d_'47''738''45'mid_38 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_38 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W./ˢ-negOne
d_'47''738''45'negOne_40 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_40 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W./ˢ-pow2
d_'47''738''45'pow2_42 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_42 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W./ˢ-zero
d_'47''738''45'zero_44 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_44 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.0<half
d_0'60'half_46 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_46 = coe MAlonzo.Code.Once.Word.du_0'60'half_146
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.0<modulus
d_0'60'modulus_48 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_48 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_144
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.0<negOne
d_0'60'negOne_50 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_50 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_348 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.1<modulus
d_1'60'modulus_52 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_52
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_628 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.2*n≡n+n
d_2'42'n'8801'n'43'n_54 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_54 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.2≤modulus
d_2'8804'modulus_56 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_56 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_344 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.Word
d_Word_58 :: ()
d_Word_58 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.fromℤ
d_fromℤ_60 :: Integer -> Integer
d_fromℤ_60
  = coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.fromℤ-0
d_fromℤ'45'0_62 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_62 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.fromℤ-in-range
d_fromℤ'45'in'45'range_64 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_64
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_152
      (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_66 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_66 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.fromℤ-neg1
d_fromℤ'45'neg1_68 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_68 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.half
d_half_70 :: Integer
d_half_70
  = coe MAlonzo.Code.Once.Word.d_half_48 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.half<modulus
d_half'60'modulus_72 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_72 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_352 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.half≡2^b
d_half'8801'2'94'b_74 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_74 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.half≤negOne
d_half'8804'negOne_76 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_76 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_372
      (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.intMin
d_intMin_78 :: Integer
d_intMin_78
  = coe MAlonzo.Code.Once.Word.d_intMin_54 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.modulus
d_modulus_80 :: Integer
d_modulus_80
  = coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_82 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_82 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.modulus≢0
d_modulus'8802'0_84 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_84
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.mod∸half≡half
d_mod'8760'half'8801'half_86 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_86 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.mod≡half+half
d_mod'8801'half'43'half_88 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_88 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.negOne
d_negOne_90 :: Integer
d_negOne_90
  = coe MAlonzo.Code.Once.Word.d_negOne_56 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.negOne<modulus
d_negOne'60'modulus_92 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_92 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_360
      (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.negOne≢0
d_negOne'8802'0_94 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_94 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.norm
d_norm_96 :: Integer -> Integer
d_norm_96
  = coe MAlonzo.Code.Once.Word.d_norm_16 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.norm-0
d_norm'45'0_98 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_98 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.norm-id
d_norm'45'id_100 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_100 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.sdiv2ᵏ
d_sdiv2'7503'_102 :: Integer -> Integer -> Integer
d_sdiv2'7503'_102
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_116 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.shlᵂ
d_shl'7490'_104 :: Integer -> Integer -> Integer
d_shl'7490'_104
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_110 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.sucNegOne≡mod
d_sucNegOne'8801'mod_106 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_106 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.tdiv-neg1
d_tdiv'45'neg1_108 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_108 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.tmod-neg1
d_tmod'45'neg1_110 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_110 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.toℤ
d_toℤ_112 :: Integer -> Integer
d_toℤ_112
  = coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.toℤ-negOne
d_toℤ'45'negOne_114 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_114 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.≡ᵇ-refl
d_'8801''7495''45'refl_116 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_116 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.≡ᵇ0-false
d_'8801''7495'0'45'false_118 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_118 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_120 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_120 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.⊕-neg
d_'8853''45'neg_122 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_122 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.⊕-neg-suc
d_'8853''45'neg'45'suc_124 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_124 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.⊕-normʳ
d_'8853''45'norm'691'_126 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_126 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.⊕≡+
d_'8853''8801''43'_128 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_128 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.⊖-normʳ
d_'8854''45'norm'691'_130 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_130 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.⊖≡∸
d_'8854''8801''8760'_132 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_132 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.⊗-pow2
d_'8855''45'pow2_134 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_134 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.⊝_
d_'8861'__136 :: Integer -> Integer
d_'8861'__136
  = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.⊝-intMin
d_'8861''45'intMin_138 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_138 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.rd
d_rd_140 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 -> Integer
d_rd_140 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_readReg_236
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_regs_396 (coe v0))
      (coe
         MAlonzo.Code.Once.Arith.Backend.RiscV64.Emit.d_arith'45'reg_10
         (coe v1))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.def
d_def_146 :: Maybe Integer -> Integer
d_def_146 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.scratch-addr
d_scratch'45'addr_150 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer
d_scratch'45'addr_150 v0 v1
  = coe
      addInt
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_readReg_236
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_regs_396 (coe v0))
         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14))
      (coe
         mulInt (coe (8 :: Integer))
         (coe
            MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.d_slot_20 (coe v1)))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.side-off
d_side'45'off_156 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22 -> Integer
d_side'45'off_156 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_24
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_26
        -> coe (8 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.path-load-go
d_path'45'load'45'go_160 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer
d_path'45'load'45'go_160
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoad.du_path'45'load'45'go_16
      (coe
         (\ v0 ->
            MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_memory_398
              (coe v0)))
      (coe d_def_146) (coe d_side'45'off_156)
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.plg-mem-cong
d_plg'45'mem'45'cong_162 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_plg'45'mem'45'cong_162 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.HeapChase
d_HeapChase_166 a0 a1 a2 = ()
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.heapchase-agree
d_heapchase'45'agree_168 ::
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.T_HeapChase_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.T_HeapChase_42
d_heapchase'45'agree_168 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.du_heapchase'45'agree_112
      v3 v5
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.plg
d_plg_170 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer
d_plg_170
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.du_plg_26
      (coe d_def_146) (coe d_side'45'off_156)
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.plg-stack-write-invisible
d_plg'45'stack'45'write'45'invisible_172 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.T_HeapChase_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_plg'45'stack'45'write'45'invisible_172 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.pathloadgo≡plg
d_pathloadgo'8801'plg_186 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pathloadgo'8801'plg_186 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.WF
d_WF_200 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 -> ()
d_WF_200 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.path-load
d_path'45'load_208 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer
d_path'45'load_208 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoad.du_path'45'load'45'go_16
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_memory_398
              (coe v2)))
      (coe d_def_146) (coe d_side'45'off_156) (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_readReg_236
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_regs_396 (coe v0))
         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42))
      (coe v1)
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.val-riscv64
d_val'45'riscv64_214 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 -> Integer
d_val'45'riscv64_214 v0 v1 ~v2 = du_val'45'riscv64_214 v0 v1
du_val'45'riscv64_214 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  Integer
du_val'45'riscv64_214 v0 v1
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
                MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_readMem_370
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_memory_398
                   (coe v1))
                (coe d_scratch'45'addr_150 (coe v1) (coe v3)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'arg_34 v2 v3
        -> coe d_path'45'load_208 (coe v1) (coe v3)
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
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.readReg-wr-arith-other
d_readReg'45'wr'45'arith'45'other_328 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_152 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readReg'45'wr'45'arith'45'other_328 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.readReg-wr-arith-same
d_readReg'45'wr'45'arith'45'same_356 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_152 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readReg'45'wr'45'arith'45'same_356 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.readReg-wr-a0-arith
d_readReg'45'wr'45'a0'45'arith_372 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_152 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readReg'45'wr'45'a0'45'arith_372 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.readReg-wr-a0-same
d_readReg'45'wr'45'a0'45'same_386 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_152 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readReg'45'wr'45'a0'45'same_386 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.rr
d_rr_392 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 -> Integer
d_rr_392 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_readReg_236
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_regs_396 (coe v0))
      (coe v1)
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.mem
d_mem_398 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  Integer -> Maybe Integer
d_mem_398 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_readMem_370
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_memory_398
         (coe v0))
      (coe v1)
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.readMem-writeMem-same
d_readMem'45'writeMem'45'same_410 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readMem'45'writeMem'45'same_410 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.sa-inj
d_sa'45'inj_442 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_sa'45'inj_442 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.wr-arith-t0
d_wr'45'arith'45't0_456 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_152 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wr'45'arith'45't0_456 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.wr-a0-t0
d_wr'45'a0'45't0_470 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_152 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wr'45'a0'45't0_470 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.sa-inv
d_sa'45'inv_488 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sa'45'inv_488 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.mem-keep
d_mem'45'keep_504 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'keep_504 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.mem-spill-hit
d_mem'45'spill'45'hit_572 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'spill'45'hit_572 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.mem-spill-miss
d_mem'45'spill'45'miss_588 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'spill'45'miss_588 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.V
d_V_600 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  Integer
d_V_600 ~v0 v1 v2 = du_V_600 v1 v2
du_V_600 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  Integer
du_V_600 v0 v1 = coe du_val'45'riscv64_214 (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.rf-other
d_rf'45'other_614 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rf'45'other_614 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.t0-inv
d_t0'45'inv_788 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_t0'45'inv_788 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.pl-inv-ns
d_pl'45'inv'45'ns_900 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pl'45'inv'45'ns_900 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.mem-agree-heap
d_mem'45'agree'45'heap_920 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'agree'45'heap_920 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.wf-e1
d_wf'45'e1_1126 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'e1_1126 ~v0 ~v1 ~v2 v3 = du_wf'45'e1_1126 v3
du_wf'45'e1_1126 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf'45'e1_1126 v0
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
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.pl-inv
d_pl'45'inv_1148 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pl'45'inv_1148 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.R
d_R_1430 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 -> ()
d_R_1430 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.R-init
d_R'45'init_1432 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'init_1432 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.R-input
d_R'45'input_1434 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 -> ()
d_R'45'input_1434 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.R-scratch
d_R'45'scratch_1436 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 -> ()
d_R'45'scratch_1436 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.R-scratch-init
d_R'45'scratch'45'init_1438 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'scratch'45'init_1438 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.R-step-arg
d_R'45'step'45'arg_1440 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
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
d_R'45'step'45'arg_1440 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.R-step-full
d_R'45'step'45'full_1442 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'step'45'full_1442 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.R-step-reload
d_R'45'step'45'reload_1444 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
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
d_R'45'step'45'reload_1444 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.Rf
d_Rf_1446 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 -> ()
d_Rf_1446 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.Rf-init
d_Rf'45'init_1448 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'init_1448 ~v0 = du_Rf'45'init_1448
du_Rf'45'init_1448 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_Rf'45'init_1448 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore.du_Rf'45'init_2104
      v3 v4
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.Rf-sim
d_Rf'45'sim_1450 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'sim_1450 ~v0 = du_Rf'45'sim_1450
du_Rf'45'sim_1450 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_Rf'45'sim_1450 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore.du_Rf'45'sim_2054
      (coe
         MAlonzo.Code.Once.Arith.Backend.RiscV64.ExecArith.du_exec1_68
         (\ v5 v6 v7 -> coe du_val'45'riscv64_214 v5 v6))
      (\ v5 v6 v7 -> coe du_wf'45'e1_1126 v7) v1 v3 v4
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.Rf-step
d_Rf'45'step_1452 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'step_1452 ~v0 = du_Rf'45'step_1452
du_Rf'45'step_1452 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_Rf'45'step_1452 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore.du_Rf'45'step_2028
      (\ v5 v6 v7 -> coe du_wf'45'e1_1126 v7) v1 v3 v4
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.arith-block-correct
d_arith'45'block'45'correct_1454 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arith'45'block'45'correct_1454 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.bin-value
d_bin'45'value_1456 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  Integer ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bin'45'value_1456 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.eb-++
d_eb'45''43''43'_1458 ::
  Integer ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eb'45''43''43'_1458 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.frame-hyp
d_frame'45'hyp_1460 ::
  Integer ->
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
d_frame'45'hyp_1460 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.input-frame
d_input'45'frame_1462 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45'frame_1462 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.no-tgt-hyp
d_no'45'tgt'45'hyp_1464 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'tgt'45'hyp_1464 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.nonspill-sf
d_nonspill'45'sf_1466 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nonspill'45'sf_1466 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.n≢j
d_n'8802'j_1468 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8802'j_1468 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.output-extract
d_output'45'extract_1470 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_output'45'extract_1470 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.result-correct
d_result'45'correct_1472 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  Integer ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result'45'correct_1472 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.sa-slot-eq
d_sa'45'slot'45'eq_1474 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sa'45'slot'45'eq_1474 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.scratch-frame
d_scratch'45'frame_1476 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
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
d_scratch'45'frame_1476 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.step-other
d_step'45'other_1478 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Maybe Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'other_1478 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.un-value
d_un'45'value_1480 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  Integer ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_un'45'value_1480 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.xreg-idx-inj
d_xreg'45'idx'45'inj_1482 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xreg'45'idx'45'inj_1482 = erased
