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
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoad
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.ExecArith
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.Arith.Machine.AbsState
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics
import qualified MAlonzo.Code.Once.Float.Arith
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg
import qualified MAlonzo.Code.Once.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W._%ˢ_
d__'37''738'__10 :: Integer -> Integer -> Integer
d__'37''738'__10
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__126 (coe (32 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W._/ˢ_
d__'47''738'__12 :: Integer -> Integer -> Integer
d__'47''738'__12
  = coe
      MAlonzo.Code.Once.Word.d__'47''738'__120 (coe (32 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W._<ˢ_
d__'60''738'__14 :: Integer -> Integer -> Bool
d__'60''738'__14
  = coe MAlonzo.Code.Once.Word.d__'60''738'__80 (coe (32 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W._≡ʷ_
d__'8801''695'__16 :: Integer -> Integer -> Bool
d__'8801''695'__16 = coe MAlonzo.Code.Once.Word.du__'8801''695'__86
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W._⊕_
d__'8853'__18 :: Integer -> Integer -> Integer
d__'8853'__18
  = coe MAlonzo.Code.Once.Word.d__'8853'__26 (coe (32 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W._⊖_
d__'8854'__20 :: Integer -> Integer -> Integer
d__'8854'__20
  = coe MAlonzo.Code.Once.Word.d__'8854'__32 (coe (32 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W._⊗_
d__'8855'__22 :: Integer -> Integer -> Integer
d__'8855'__22
  = coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe (32 :: Integer))
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
      MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_604
      (coe (32 :: Integer)) v2 v3 v4
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
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_570
      (coe (32 :: Integer)) v2 v3
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
      MAlonzo.Code.Once.Word.du_0'60'negOne_426 (coe (32 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.1<modulus
d_1'60'modulus_52 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_52
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_796 (coe (32 :: Integer))
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
      MAlonzo.Code.Once.Word.du_2'8804'modulus_422 (coe (32 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.<⇒<ᵇtrue
d_'60''8658''60''7495'true_58 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8658''60''7495'true_58 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.InRange
d_InRange_60 :: Integer -> ()
d_InRange_60 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.Word
d_Word_62 :: ()
d_Word_62 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.fromℤ
d_fromℤ_64 :: Integer -> Integer
d_fromℤ_64
  = coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (32 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.fromℤ-0
d_fromℤ'45'0_66 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_66 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.fromℤ-in-range
d_fromℤ'45'in'45'range_68 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_68
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_174
      (coe (32 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_70 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_70 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.fromℤ-neg1
d_fromℤ'45'neg1_72 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_72 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.half
d_half_74 :: Integer
d_half_74
  = coe MAlonzo.Code.Once.Word.d_half_48 (coe (32 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.half<modulus
d_half'60'modulus_76 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_76 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_430 (coe (32 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.half≡2^b
d_half'8801'2'94'b_78 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_78 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.half≤negOne
d_half'8804'negOne_80 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_80 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_450
      (coe (32 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.inRange?
d_inRange'63'_82 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_82
  = coe MAlonzo.Code.Once.Word.d_inRange'63'_62 (coe (32 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.intMin
d_intMin_84 :: Integer
d_intMin_84
  = coe MAlonzo.Code.Once.Word.d_intMin_54 (coe (32 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.lit-hi
d_lit'45'hi_86 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'hi_86 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Word.du_lit'45'hi_654 v3
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.lit-lo
d_lit'45'lo_88 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'lo_88 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_lit'45'lo_666 (coe (32 :: Integer)) v2 v3
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.modulus
d_modulus_90 :: Integer
d_modulus_90
  = coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (32 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_92 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_92 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.modulus≢0
d_modulus'8802'0_94 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_94
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12 (coe (32 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.mod∸half≡half
d_mod'8760'half'8801'half_96 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_96 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.mod≡half+half
d_mod'8801'half'43'half_98 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_98 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.negOne
d_negOne_100 :: Integer
d_negOne_100
  = coe MAlonzo.Code.Once.Word.d_negOne_78 (coe (32 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.negOne<modulus
d_negOne'60'modulus_102 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_102 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_438
      (coe (32 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.negOne≢0
d_negOne'8802'0_104 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_104 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.norm
d_norm_106 :: Integer -> Integer
d_norm_106
  = coe MAlonzo.Code.Once.Word.d_norm_16 (coe (32 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.norm-0
d_norm'45'0_108 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_108 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.norm-id
d_norm'45'id_110 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_110 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.sbb-pos
d_sbb'45'pos_112 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sbb'45'pos_112 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.sbb-zero
d_sbb'45'zero_114 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sbb'45'zero_114 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.sdiv2ᵏ
d_sdiv2'7503'_116 :: Integer -> Integer -> Integer
d_sdiv2'7503'_116
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_138 (coe (32 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.shlᵂ
d_shl'7490'_118 :: Integer -> Integer -> Integer
d_shl'7490'_118
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_132 (coe (32 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.sucNegOne≡mod
d_sucNegOne'8801'mod_120 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_120 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.tdiv-neg1
d_tdiv'45'neg1_122 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_122 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.tmod-neg1
d_tmod'45'neg1_124 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_124 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.toWord
d_toWord_126 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_126 v0 v1
  = coe MAlonzo.Code.Once.Word.du_toWord_68 (coe (32 :: Integer)) v0
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.toWord≡fromℤ
d_toWord'8801'fromℤ_128 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'8801'fromℤ_128 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.toℤ
d_toℤ_130 :: Integer -> Integer
d_toℤ_130
  = coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe (32 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.toℤ-negOne
d_toℤ'45'negOne_132 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_132 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.toℤ∘fromℤ
d_toℤ'8728'fromℤ_134 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'8728'fromℤ_134 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.unplus
d_unplus_136 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_unplus_136 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Word.du_unplus_648 v4
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.≡ᵇ-refl
d_'8801''7495''45'refl_138 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_138 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.≡ᵇ0-false
d_'8801''7495'0'45'false_140 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_140 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_142 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_142 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊕-neg
d_'8853''45'neg_144 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_144 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊕-neg-suc
d_'8853''45'neg'45'suc_146 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_146 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊕-normʳ
d_'8853''45'norm'691'_148 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_148 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊕≡+
d_'8853''8801''43'_150 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_150 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊖-normʳ
d_'8854''45'norm'691'_152 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_152 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊖-self
d_'8854''45'self_154 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'self_154 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊖≡∸
d_'8854''8801''8760'_156 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_156 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊗-pow2
d_'8855''45'pow2_158 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_158 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊝_
d_'8861'__160 :: Integer -> Integer
d_'8861'__160
  = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe (32 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊝-fromℤ
d_'8861''45'fromℤ_162 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'fromℤ_162 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊝-intMin
d_'8861''45'intMin_164 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_164 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.W.⊝-invol-norm
d_'8861''45'invol'45'norm_166 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'invol'45'norm_166 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.NonSpill
d_NonSpill_170 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 -> ()
d_NonSpill_170 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.additive-sa-inj
d_additive'45'sa'45'inj_172 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_additive'45'sa'45'inj_172 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.tgt
d_tgt_174 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  Maybe MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10
d_tgt_174
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore.du_tgt_44
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.¬d≡x
d_'172'd'8801'x_176 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172'd'8801'x_176 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.R
d_R_180 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny -> ()
d_R_180 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.R-init
d_R'45'init_182 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'init_182 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.R-input
d_R'45'input_184 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny -> ()
d_R'45'input_184 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.R-scratch
d_R'45'scratch_186 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny -> ()
d_R'45'scratch_186 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.R-scratch-init
d_R'45'scratch'45'init_188 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'scratch'45'init_188 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.R-step-arg
d_R'45'step'45'arg_190 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
   MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'step'45'arg_190 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.R-step-farg
d_R'45'step'45'farg_192 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
   MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'step'45'farg_192 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.R-step-full
d_R'45'step'45'full_194 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'step'45'full_194 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.R-step-reload
d_R'45'step'45'reload_196 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
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
d_R'45'step'45'reload_196 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.Rf
d_Rf_198 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny -> ()
d_Rf_198 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.Rf-init
d_Rf'45'init_200 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
   MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'init_200 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31
                 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48
                 v49 v50 v51 v52
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore.du_Rf'45'init_3484
      v51 v52
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.Rf-sim
d_Rf'45'sim_202 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'sim_202 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31
                v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48
                v49 v50 v51 v52 v53
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore.du_Rf'45'sim_3428
      v10 v20 v49 v50 v52 v53
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.Rf-step
d_Rf'45'step_204 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'step_204 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31
                 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48
                 v49 v50 v51 v52 v53
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore.du_Rf'45'step_3400
      v20 v49 v52 v53
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.arith-block-correct
d_arith'45'block'45'correct_206 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
   MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arith'45'block'45'correct_206 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.bin-value
d_bin'45'value_208 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  Integer ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bin'45'value_208 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.eb-++
d_eb'45''43''43'_210 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eb'45''43''43'_210 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.frame-hyp
d_frame'45'hyp_212 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
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
d_frame'45'hyp_212 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.input-frame
d_input'45'frame_214 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
   MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45'frame_214 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.leafWord
d_leafWord_216 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  AgdaAny -> Integer
d_leafWord_216 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
               v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31
               v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48
               v49 v50 v51
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore.du_leafWord_1316
      (coe
         MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_78
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10))
      v48 v50 v51
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.leafWord-flt
d_leafWord'45'flt_218 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leafWord'45'flt_218 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.leafWord-int
d_leafWord'45'int_220 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leafWord'45'int_220 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.no-tgt-hyp
d_no'45'tgt'45'hyp_222 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'tgt'45'hyp_222 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.nonspill-sf
d_nonspill'45'sf_224 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nonspill'45'sf_224 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.n≢j
d_n'8802'j_226 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8802'j_226 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.output-extract
d_output'45'extract_228 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_output'45'extract_228 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.result-correct
d_result'45'correct_230 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  Integer ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result'45'correct_230 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.sa-slot-eq
d_sa'45'slot'45'eq_232 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sa'45'slot'45'eq_232 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.scratch-frame
d_scratch'45'frame_234 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
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
d_scratch'45'frame_234 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.step-other
d_step'45'other_236 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Maybe Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'other_236 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.un-value
d_un'45'value_238 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  Integer ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_un'45'value_238 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Core.xreg-idx-inj
d_xreg'45'idx'45'inj_240 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xreg'45'idx'45'inj_240 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.rd
d_rd_242 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 -> Integer
d_rd_242 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_readReg_208
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_regs_308
         (coe v0))
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit.d_arith'45'reg_10
         (coe v1))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.def
d_def_248 :: Maybe Integer -> Integer
d_def_248 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.scratch-addr
d_scratch'45'addr_252 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer
d_scratch'45'addr_252 v0 v1
  = coe
      addInt
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_readReg_208
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_regs_308
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
      (coe
         mulInt (coe (4 :: Integer))
         (coe
            MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.d_slot_20 (coe v1)))
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.side-off
d_side'45'off_258 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24 -> Integer
d_side'45'off_258 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_26
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_28
        -> coe (4 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.path-load-go
d_path'45'load'45'go_262 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer
d_path'45'load'45'go_262
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoad.du_path'45'load'45'go_16
      (coe
         (\ v0 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_memory_310
              (coe v0)))
      (coe d_def_248) (coe d_side'45'off_258)
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.plg-mem-cong
d_plg'45'mem'45'cong_264 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_plg'45'mem'45'cong_264 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.path-load
d_path'45'load_266 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer
d_path'45'load_266 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoad.du_path'45'load'45'go_16
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_memory_310
              (coe v2)))
      (coe d_def_248) (coe d_side'45'off_258) (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_readReg_208
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_regs_308
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14))
      (coe v1)
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.val-x86-32
d_val'45'x86'45'32_272 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer
d_val'45'x86'45'32_272 v0 v1 ~v2 = du_val'45'x86'45'32_272 v0 v1
du_val'45'x86'45'32_272 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  Integer
du_val'45'x86'45'32_272 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'imm_26 v2 v3
        -> coe
             MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (32 :: Integer)) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_28 v2 v3
        -> coe d_rd_242 (coe v1) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'r'45'm_30 v2 v3
        -> coe d_rd_242 (coe v1) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'm'45'r_32 v2 v3
        -> coe
             d_def_248
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_readMem_264
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_memory_310
                   (coe v1))
                (coe d_scratch'45'addr_252 (coe v1) (coe v3)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'arg_34 v2 v3
        -> coe d_path'45'load_266 (coe v1) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xadd'45'rr_36 v2 v3
        -> coe
             MAlonzo.Code.Once.Word.d__'8853'__26 (coe (32 :: Integer))
             (coe d_rd_242 (coe v1) (coe v2)) (coe d_rd_242 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsub'45'rr_38 v2 v3
        -> coe
             MAlonzo.Code.Once.Word.d__'8854'__32 (coe (32 :: Integer))
             (coe d_rd_242 (coe v1) (coe v2)) (coe d_rd_242 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Ximul'45'rr_40 v2 v3
        -> coe
             MAlonzo.Code.Once.Word.d__'8855'__38 (coe (32 :: Integer))
             (coe d_rd_242 (coe v1) (coe v2)) (coe d_rd_242 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xneg'45'r_42 v2
        -> coe
             MAlonzo.Code.Once.Word.d_'8861'__44 (coe (32 :: Integer))
             (coe d_rd_242 (coe v1) (coe v2))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'rrr_44 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'47''738'__120 (coe (32 :: Integer))
             (coe d_rd_242 (coe v1) (coe v3)) (coe d_rd_242 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'rrr_46 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'37''738'__126 (coe (32 :: Integer))
             (coe d_rd_242 (coe v1) (coe v3)) (coe d_rd_242 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xcmp'45'rrr_48 v2 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Arith.CmpOp.d_cmp'45'bit_62 (coe (32 :: Integer))
             (coe v2) (coe d_rd_242 (coe v1) (coe v4))
             (coe d_rd_242 (coe v1) (coe v5))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'safe'45'rrr_50 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'47''738'__120 (coe (32 :: Integer))
             (coe d_rd_242 (coe v1) (coe v3)) (coe d_rd_242 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'safe'45'rrr_52 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'37''738'__126 (coe (32 :: Integer))
             (coe d_rd_242 (coe v1) (coe v3)) (coe d_rd_242 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xshl'45'rri_54 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d_shl'7490'_132 (coe (32 :: Integer))
             (coe d_rd_242 (coe v1) (coe v3)) (coe v4)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsdiv'45'pow2'45'rri_56 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d_sdiv2'7503'_138 (coe (32 :: Integer))
             (coe d_rd_242 (coe v1) (coe v3)) (coe v4)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfadd'45'rr_58 v2 v3
        -> coe
             MAlonzo.Code.Once.Float.Arith.d_fadd_314
             (coe MAlonzo.Code.Once.Float.Dyadic.d_binary32_40)
             (coe d_rd_242 (coe v1) (coe v2)) (coe d_rd_242 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsub'45'rr_60 v2 v3
        -> coe
             MAlonzo.Code.Once.Float.Arith.d_fsub_316
             (coe MAlonzo.Code.Once.Float.Dyadic.d_binary32_40)
             (coe d_rd_242 (coe v1) (coe v2)) (coe d_rd_242 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfmul'45'rr_62 v2 v3
        -> coe
             MAlonzo.Code.Once.Float.Arith.d_fmul_318
             (coe MAlonzo.Code.Once.Float.Dyadic.d_binary32_40)
             (coe d_rd_242 (coe v1) (coe v2)) (coe d_rd_242 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfdiv'45'rrr_64 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Float.Arith.d_fdiv_320
             (coe MAlonzo.Code.Once.Float.Dyadic.d_binary32_40)
             (coe d_rd_242 (coe v1) (coe v3)) (coe d_rd_242 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsubr'45'rr_66 v2 v3
        -> coe
             MAlonzo.Code.Once.Float.Arith.d_fsub_316
             (coe MAlonzo.Code.Once.Float.Dyadic.d_binary32_40)
             (coe d_rd_242 (coe v1) (coe v3)) (coe d_rd_242 (coe v1) (coe v2))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfneg'45'r_68 v2
        -> coe
             MAlonzo.Code.Once.Float.Arith.d_fneg_356
             (coe MAlonzo.Code.Once.Float.Dyadic.d_binary32_40)
             (coe d_rd_242 (coe v1) (coe v2))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xi2f'45'r_70 v2 v3
        -> coe
             MAlonzo.Code.Once.Float.Arith.d_i2f_362
             (coe MAlonzo.Code.Once.Float.Dyadic.d_binary32_40)
             (coe
                MAlonzo.Code.Once.Word.d_toℤ_50 (coe (32 :: Integer))
                (coe d_rd_242 (coe v1) (coe v3)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'fimm_72 v2 v3
        -> coe
             MAlonzo.Code.Once.Float.Decimal.d_round_174
             (coe MAlonzo.Code.Once.Float.Dyadic.d_binary32_40) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'farg_74 v2 v3
        -> coe d_path'45'load_266 (coe v1) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'out_76 v2
        -> coe d_rd_242 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.readReg-wr-arith-other
d_readReg'45'wr'45'arith'45'other_458 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_172 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readReg'45'wr'45'arith'45'other_458 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.readReg-wr-arith-same
d_readReg'45'wr'45'arith'45'same_486 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_172 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readReg'45'wr'45'arith'45'same_486 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.readReg-wr-eax-arith
d_readReg'45'wr'45'eax'45'arith_502 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_172 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readReg'45'wr'45'eax'45'arith_502 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.readReg-wr-eax-same
d_readReg'45'wr'45'eax'45'same_516 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_172 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readReg'45'wr'45'eax'45'same_516 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.wr-arith-esp
d_wr'45'arith'45'esp_528 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_172 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wr'45'arith'45'esp_528 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.wr-eax-esp
d_wr'45'eax'45'esp_542 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_172 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wr'45'eax'45'esp_542 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.wr-arith-ecx
d_wr'45'arith'45'ecx_554 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_172 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wr'45'arith'45'ecx_554 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.wr-eax-ecx
d_wr'45'eax'45'ecx_568 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_172 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wr'45'eax'45'ecx_568 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.rr
d_rr_574 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer
d_rr_574 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_readReg_208
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_regs_308
         (coe v0))
      (coe v1)
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.mem
d_mem_580 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  Integer -> Maybe Integer
d_mem_580 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_readMem_264
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_memory_310
         (coe v0))
      (coe v1)
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.V
d_V_586 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  Integer
d_V_586 v0 v1 = coe du_val'45'x86'45'32_272 (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.rf-other
d_rf'45'other_600 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rf'45'other_600 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.readMem-writeMem-same
d_readMem'45'writeMem'45'same_880 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readMem'45'writeMem'45'same_880 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.readMem-writeMem-other
d_readMem'45'writeMem'45'other_914 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readMem'45'writeMem'45'other_914 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.sa-inj
d_sa'45'inj_962 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_sa'45'inj_962 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.safe-inv
d_safe'45'inv_986 ::
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
  (MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_172 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_172 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_safe'45'inv_986 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.sa-inv
d_sa'45'inv_1318 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sa'45'inv_1318 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.mem-keep
d_mem'45'keep_1334 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'keep_1334 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.mem-spill-hit
d_mem'45'spill'45'hit_1442 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'spill'45'hit_1442 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.mem-spill-miss
d_mem'45'spill'45'miss_1458 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'spill'45'miss_1458 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.pl-inv-ns
d_pl'45'inv'45'ns_1476 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pl'45'inv'45'ns_1476 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.HeapChase
d_HeapChase_1490 a0 a1 a2 = ()
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.heapchase-agree
d_heapchase'45'agree_1492 ::
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.T_HeapChase_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.T_HeapChase_42
d_heapchase'45'agree_1492 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.du_heapchase'45'agree_112
      v3 v5
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.plg
d_plg_1494 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer
d_plg_1494
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.du_plg_26
      (coe d_def_248) (coe d_side'45'off_258)
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.plg-stack-write-invisible
d_plg'45'stack'45'write'45'invisible_1496 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.T_HeapChase_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_plg'45'stack'45'write'45'invisible_1496 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.WF
d_WF_1504 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 -> ()
d_WF_1504 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.pathloadgo≡plg
d_pathloadgo'8801'plg_1518 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pathloadgo'8801'plg_1518 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.mem-agree-heap
d_mem'45'agree'45'heap_1540 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'agree'45'heap_1540 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32.wf-e1
d_wf'45'e1_1870 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'e1_1870 ~v0 ~v1 v2 = du_wf'45'e1_1870 v2
du_wf'45'e1_1870 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf'45'e1_1870 v0
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
d_pl'45'inv_1892 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pl'45'inv_1892 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R
d_R_2342 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 -> ()
d_R_2342 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R-init
d_R'45'init_2344 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'init_2344 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R-input
d_R'45'input_2346 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 -> ()
d_R'45'input_2346 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R-scratch
d_R'45'scratch_2348 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 -> ()
d_R'45'scratch_2348 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R-scratch-init
d_R'45'scratch'45'init_2350 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'scratch'45'init_2350 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R-step-arg
d_R'45'step'45'arg_2352 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
   MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'step'45'arg_2352 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R-step-farg
d_R'45'step'45'farg_2354 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
   MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'step'45'farg_2354 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R-step-full
d_R'45'step'45'full_2356 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'step'45'full_2356 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.R-step-reload
d_R'45'step'45'reload_2358 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
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
d_R'45'step'45'reload_2358 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Rf
d_Rf_2360 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 -> ()
d_Rf_2360 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Rf-init
d_Rf'45'init_2362 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
   MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'init_2362 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore.du_Rf'45'init_3484
      v3 v4
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Rf-sim
d_Rf'45'sim_2364 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'sim_2364 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore.du_Rf'45'sim_3428
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.ExecArith.d_exec1_116
         (\ v6 v7 v8 -> coe du_val'45'x86'45'32_272 v6 v7))
      (\ v6 v7 v8 -> coe du_wf'45'e1_1870 v8) v1 v2 v4 v5
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.Rf-step
d_Rf'45'step_2366 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'step_2366 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore.du_Rf'45'step_3400
      (\ v6 v7 v8 -> coe du_wf'45'e1_1870 v8) v1 v4 v5
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.arith-block-correct
d_arith'45'block'45'correct_2368 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
   MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arith'45'block'45'correct_2368 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.bin-value
d_bin'45'value_2370 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  Integer ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bin'45'value_2370 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.eb-++
d_eb'45''43''43'_2372 ::
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eb'45''43''43'_2372 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.frame-hyp
d_frame'45'hyp_2374 ::
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
d_frame'45'hyp_2374 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.input-frame
d_input'45'frame_2376 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
   MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45'frame_2376 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.leafWord
d_leafWord_2378 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  AgdaAny -> Integer
d_leafWord_2378 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore.du_leafWord_1316
      (coe
         MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_78
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10))
      v0 v2 v3
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.leafWord-flt
d_leafWord'45'flt_2380 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leafWord'45'flt_2380 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.leafWord-int
d_leafWord'45'int_2382 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leafWord'45'int_2382 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.no-tgt-hyp
d_no'45'tgt'45'hyp_2384 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'tgt'45'hyp_2384 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.nonspill-sf
d_nonspill'45'sf_2386 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nonspill'45'sf_2386 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.n≢j
d_n'8802'j_2388 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8802'j_2388 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.output-extract
d_output'45'extract_2390 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_output'45'extract_2390 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.result-correct
d_result'45'correct_2392 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  Integer ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result'45'correct_2392 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.sa-slot-eq
d_sa'45'slot'45'eq_2394 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sa'45'slot'45'eq_2394 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.scratch-frame
d_scratch'45'frame_2396 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
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
d_scratch'45'frame_2396 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.step-other
d_step'45'other_2398 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Maybe Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'other_2398 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.un-value
d_un'45'value_2400 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  Integer ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_un'45'value_2400 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimX86-32._.xreg-idx-inj
d_xreg'45'idx'45'inj_2402 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xreg'45'idx'45'inj_2402 = erased
