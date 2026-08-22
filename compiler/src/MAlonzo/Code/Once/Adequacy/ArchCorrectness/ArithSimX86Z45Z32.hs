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
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W._%ˢ_
d__'37''738'__10 :: Integer -> Integer -> Integer
d__'37''738'__10
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__126 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W._/ˢ_
d__'47''738'__12 :: Integer -> Integer -> Integer
d__'47''738'__12
  = coe
      MAlonzo.Code.Once.Word.d__'47''738'__120 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W._<ˢ_
d__'60''738'__14 :: Integer -> Integer -> Bool
d__'60''738'__14
  = coe MAlonzo.Code.Once.Word.d__'60''738'__80 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W._≡ʷ_
d__'8801''695'__16 :: Integer -> Integer -> Bool
d__'8801''695'__16 = coe MAlonzo.Code.Once.Word.du__'8801''695'__86
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
      MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_548
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
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_514
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
d_0'60'half_46 = coe MAlonzo.Code.Once.Word.du_0'60'half_168
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.0<modulus
d_0'60'modulus_48 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_48 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_166
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.0<negOne
d_0'60'negOne_50 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_50 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_370 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.1<modulus
d_1'60'modulus_52 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_52
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_650 (coe (64 :: Integer))
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
      MAlonzo.Code.Once.Word.du_2'8804'modulus_366 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.InRange
d_InRange_58 :: Integer -> ()
d_InRange_58 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.Word
d_Word_60 :: ()
d_Word_60 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.fromℤ
d_fromℤ_62 :: Integer -> Integer
d_fromℤ_62
  = coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.fromℤ-0
d_fromℤ'45'0_64 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_64 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.fromℤ-in-range
d_fromℤ'45'in'45'range_66 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_66
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_174
      (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_68 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_68 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.fromℤ-neg1
d_fromℤ'45'neg1_70 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_70 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.half
d_half_72 :: Integer
d_half_72
  = coe MAlonzo.Code.Once.Word.d_half_48 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.half<modulus
d_half'60'modulus_74 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_74 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_374 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.half≡2^b
d_half'8801'2'94'b_76 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_76 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.half≤negOne
d_half'8804'negOne_78 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_78 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_394
      (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.inRange?
d_inRange'63'_80 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_80
  = coe MAlonzo.Code.Once.Word.d_inRange'63'_62 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.intMin
d_intMin_82 :: Integer
d_intMin_82
  = coe MAlonzo.Code.Once.Word.d_intMin_54 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.modulus
d_modulus_84 :: Integer
d_modulus_84
  = coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_86 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_86 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.modulus≢0
d_modulus'8802'0_88 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_88
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.mod∸half≡half
d_mod'8760'half'8801'half_90 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_90 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.mod≡half+half
d_mod'8801'half'43'half_92 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_92 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.negOne
d_negOne_94 :: Integer
d_negOne_94
  = coe MAlonzo.Code.Once.Word.d_negOne_78 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.negOne<modulus
d_negOne'60'modulus_96 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_96 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_382
      (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.negOne≢0
d_negOne'8802'0_98 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_98 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.norm
d_norm_100 :: Integer -> Integer
d_norm_100
  = coe MAlonzo.Code.Once.Word.d_norm_16 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.norm-0
d_norm'45'0_102 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_102 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.norm-id
d_norm'45'id_104 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_104 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.sdiv2ᵏ
d_sdiv2'7503'_106 :: Integer -> Integer -> Integer
d_sdiv2'7503'_106
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_138 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.shlᵂ
d_shl'7490'_108 :: Integer -> Integer -> Integer
d_shl'7490'_108
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_132 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.sucNegOne≡mod
d_sucNegOne'8801'mod_110 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_110 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.tdiv-neg1
d_tdiv'45'neg1_112 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_112 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.tmod-neg1
d_tmod'45'neg1_114 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_114 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.toWord
d_toWord_116 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_116 v0 v1
  = coe MAlonzo.Code.Once.Word.du_toWord_68 (coe (64 :: Integer)) v0
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.toWord≡fromℤ
d_toWord'8801'fromℤ_118 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'8801'fromℤ_118 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.toℤ
d_toℤ_120 :: Integer -> Integer
d_toℤ_120
  = coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.toℤ-negOne
d_toℤ'45'negOne_122 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_122 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.≡ᵇ-refl
d_'8801''7495''45'refl_124 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_124 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.≡ᵇ0-false
d_'8801''7495'0'45'false_126 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_126 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_128 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_128 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊕-neg
d_'8853''45'neg_130 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_130 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊕-neg-suc
d_'8853''45'neg'45'suc_132 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_132 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊕-normʳ
d_'8853''45'norm'691'_134 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_134 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊕≡+
d_'8853''8801''43'_136 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_136 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊖-normʳ
d_'8854''45'norm'691'_138 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_138 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊖≡∸
d_'8854''8801''8760'_140 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_140 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊗-pow2
d_'8855''45'pow2_142 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_142 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊝_
d_'8861'__144 :: Integer -> Integer
d_'8861'__144
  = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊝-intMin
d_'8861''45'intMin_146 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_146 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.rd
d_rd_148 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 -> Integer
d_rd_148 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_readReg_188
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_regs_288
         (coe v0))
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit.d_arith'45'reg_10
         (coe v1))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.def
d_def_154 :: Maybe Integer -> Integer
d_def_154 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.scratch-addr
d_scratch'45'addr_158 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer
d_scratch'45'addr_158 v0 v1
  = coe
      addInt
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_readReg_188
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_regs_288
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
      (coe
         mulInt (coe (4 :: Integer))
         (coe
            MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.d_slot_20 (coe v1)))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.side-off
d_side'45'off_164 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22 -> Integer
d_side'45'off_164 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_24
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_26
        -> coe (4 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.path-load-go
d_path'45'load'45'go_168 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer
d_path'45'load'45'go_168
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoad.du_path'45'load'45'go_16
      (coe
         (\ v0 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_memory_290
              (coe v0)))
      (coe d_def_154) (coe d_side'45'off_164)
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.plg-mem-cong
d_plg'45'mem'45'cong_170 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_plg'45'mem'45'cong_170 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.path-load
d_path'45'load_172 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer
d_path'45'load_172 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoad.du_path'45'load'45'go_16
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_memory_290
              (coe v2)))
      (coe d_def_154) (coe d_side'45'off_164) (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_readReg_188
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_regs_288
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14))
      (coe v1)
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.val-x86-32
d_val'45'x86'45'32_178 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer
d_val'45'x86'45'32_178 v0 v1 ~v2 = du_val'45'x86'45'32_178 v0 v1
du_val'45'x86'45'32_178 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  Integer
du_val'45'x86'45'32_178 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'imm_26 v2 v3
        -> coe
             MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer)) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_28 v2 v3
        -> coe d_rd_148 (coe v1) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'r'45'm_30 v2 v3
        -> coe d_rd_148 (coe v1) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'm'45'r_32 v2 v3
        -> coe
             d_def_154
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_readMem_244
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_memory_290
                   (coe v1))
                (coe d_scratch'45'addr_158 (coe v1) (coe v3)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'arg_34 v2 v3
        -> coe d_path'45'load_172 (coe v1) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xadd'45'rr_36 v2 v3
        -> coe
             MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer))
             (coe d_rd_148 (coe v1) (coe v2)) (coe d_rd_148 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsub'45'rr_38 v2 v3
        -> coe
             MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
             (coe d_rd_148 (coe v1) (coe v2)) (coe d_rd_148 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Ximul'45'rr_40 v2 v3
        -> coe
             MAlonzo.Code.Once.Word.d__'8855'__38 (coe (64 :: Integer))
             (coe d_rd_148 (coe v1) (coe v2)) (coe d_rd_148 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xneg'45'r_42 v2
        -> coe
             MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
             (coe d_rd_148 (coe v1) (coe v2))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'rrr_44 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'47''738'__120 (coe (64 :: Integer))
             (coe d_rd_148 (coe v1) (coe v3)) (coe d_rd_148 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'rrr_46 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'37''738'__126 (coe (64 :: Integer))
             (coe d_rd_148 (coe v1) (coe v3)) (coe d_rd_148 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'safe'45'rrr_48 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'47''738'__120 (coe (64 :: Integer))
             (coe d_rd_148 (coe v1) (coe v3)) (coe d_rd_148 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'safe'45'rrr_50 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'37''738'__126 (coe (64 :: Integer))
             (coe d_rd_148 (coe v1) (coe v3)) (coe d_rd_148 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xshl'45'rri_52 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d_shl'7490'_132 (coe (64 :: Integer))
             (coe d_rd_148 (coe v1) (coe v3)) (coe v4)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsdiv'45'pow2'45'rri_54 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d_sdiv2'7503'_138 (coe (64 :: Integer))
             (coe d_rd_148 (coe v1) (coe v3)) (coe v4)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'out_56 v2
        -> coe d_rd_148 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.readReg-wr-arith-other
d_readReg'45'wr'45'arith'45'other_292 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_152 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readReg'45'wr'45'arith'45'other_292 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.readReg-wr-arith-same
d_readReg'45'wr'45'arith'45'same_320 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_152 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readReg'45'wr'45'arith'45'same_320 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.readReg-wr-eax-arith
d_readReg'45'wr'45'eax'45'arith_336 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_152 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readReg'45'wr'45'eax'45'arith_336 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.readReg-wr-eax-same
d_readReg'45'wr'45'eax'45'same_350 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_152 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readReg'45'wr'45'eax'45'same_350 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.wr-arith-esp
d_wr'45'arith'45'esp_362 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_152 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wr'45'arith'45'esp_362 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.wr-eax-esp
d_wr'45'eax'45'esp_376 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_152 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wr'45'eax'45'esp_376 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.wr-arith-ecx
d_wr'45'arith'45'ecx_388 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_152 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wr'45'arith'45'ecx_388 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.wr-eax-ecx
d_wr'45'eax'45'ecx_402 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_152 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wr'45'eax'45'ecx_402 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.rr
d_rr_408 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer
d_rr_408 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_readReg_188
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_regs_288
         (coe v0))
      (coe v1)
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.mem
d_mem_414 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  Integer -> Maybe Integer
d_mem_414 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_readMem_244
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_memory_290
         (coe v0))
      (coe v1)
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.V
d_V_420 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  Integer
d_V_420 v0 v1 = coe du_val'45'x86'45'32_178 (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.rf-other
d_rf'45'other_434 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rf'45'other_434 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.readMem-writeMem-same
d_readMem'45'writeMem'45'same_610 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readMem'45'writeMem'45'same_610 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.readMem-writeMem-other
d_readMem'45'writeMem'45'other_644 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readMem'45'writeMem'45'other_644 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.sa-inj
d_sa'45'inj_692 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_sa'45'inj_692 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.safe-inv
d_safe'45'inv_716 ::
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  (MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_152 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_152 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_safe'45'inv_716 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.sa-inv
d_sa'45'inv_924 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sa'45'inv_924 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.mem-keep
d_mem'45'keep_940 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'keep_940 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.mem-spill-hit
d_mem'45'spill'45'hit_1008 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'spill'45'hit_1008 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.mem-spill-miss
d_mem'45'spill'45'miss_1024 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'spill'45'miss_1024 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.pl-inv-ns
d_pl'45'inv'45'ns_1042 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pl'45'inv'45'ns_1042 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.HeapChase
d_HeapChase_1056 a0 a1 a2 = ()
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.heapchase-agree
d_heapchase'45'agree_1058 ::
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.T_HeapChase_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.T_HeapChase_42
d_heapchase'45'agree_1058 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.du_heapchase'45'agree_112
      v3 v5
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.plg
d_plg_1060 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer
d_plg_1060
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.du_plg_26
      (coe d_def_154) (coe d_side'45'off_164)
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.plg-stack-write-invisible
d_plg'45'stack'45'write'45'invisible_1062 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.T_HeapChase_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_plg'45'stack'45'write'45'invisible_1062 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.WF
d_WF_1070 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 -> ()
d_WF_1070 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.pathloadgo≡plg
d_pathloadgo'8801'plg_1084 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pathloadgo'8801'plg_1084 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.mem-agree-heap
d_mem'45'agree'45'heap_1106 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'agree'45'heap_1106 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.wf-e1
d_wf'45'e1_1312 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'e1_1312 ~v0 ~v1 v2 = du_wf'45'e1_1312 v2
du_wf'45'e1_1312 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf'45'e1_1312 v0
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
d_pl'45'inv_1334 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pl'45'inv_1334 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R
d_R_1616 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 -> ()
d_R_1616 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R-init
d_R'45'init_1618 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'init_1618 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R-input
d_R'45'input_1620 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 -> ()
d_R'45'input_1620 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R-scratch
d_R'45'scratch_1622 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 -> ()
d_R'45'scratch_1622 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R-scratch-init
d_R'45'scratch'45'init_1624 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'scratch'45'init_1624 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R-step-arg
d_R'45'step'45'arg_1626 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
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
d_R'45'step'45'arg_1626 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R-step-full
d_R'45'step'45'full_1628 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'step'45'full_1628 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R-step-reload
d_R'45'step'45'reload_1630 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
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
d_R'45'step'45'reload_1630 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Rf
d_Rf_1632 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 -> ()
d_Rf_1632 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Rf-init
d_Rf'45'init_1634 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'init_1634 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore.du_Rf'45'init_2104
      v3 v4
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Rf-sim
d_Rf'45'sim_1636 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'sim_1636 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore.du_Rf'45'sim_2054
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.ExecArith.d_exec1_82
         (\ v5 v6 v7 -> coe du_val'45'x86'45'32_178 v5 v6))
      (\ v5 v6 v7 -> coe du_wf'45'e1_1312 v7) v1 v3 v4
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Rf-step
d_Rf'45'step_1638 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'step_1638 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore.du_Rf'45'step_2028
      (\ v5 v6 v7 -> coe du_wf'45'e1_1312 v7) v1 v3 v4
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.arith-block-correct
d_arith'45'block'45'correct_1640 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arith'45'block'45'correct_1640 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.bin-value
d_bin'45'value_1642 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  Integer ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bin'45'value_1642 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.eb-++
d_eb'45''43''43'_1644 ::
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eb'45''43''43'_1644 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.frame-hyp
d_frame'45'hyp_1646 ::
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
d_frame'45'hyp_1646 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.input-frame
d_input'45'frame_1648 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45'frame_1648 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.no-tgt-hyp
d_no'45'tgt'45'hyp_1650 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'tgt'45'hyp_1650 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.nonspill-sf
d_nonspill'45'sf_1652 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nonspill'45'sf_1652 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.n≢j
d_n'8802'j_1654 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8802'j_1654 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.output-extract
d_output'45'extract_1656 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_output'45'extract_1656 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.result-correct
d_result'45'correct_1658 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  Integer ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result'45'correct_1658 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.sa-slot-eq
d_sa'45'slot'45'eq_1660 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sa'45'slot'45'eq_1660 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.scratch-frame
d_scratch'45'frame_1662 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
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
d_scratch'45'frame_1662 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.step-other
d_step'45'other_1664 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Maybe Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'other_1664 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.un-value
d_un'45'value_1666 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_276 ->
  Integer ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_un'45'value_1666 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.xreg-idx-inj
d_xreg'45'idx'45'inj_1668 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xreg'45'idx'45'inj_1668 = erased
