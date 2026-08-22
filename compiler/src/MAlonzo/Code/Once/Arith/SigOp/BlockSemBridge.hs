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

module MAlonzo.Code.Once.Arith.SigOp.BlockSemBridge where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.Machine.WordSem
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Arith.SigOp.BlockSemBridge._.eval-arith-W
d_eval'45'arith'45'W_10 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> Integer
d_eval'45'arith'45'W_10
  = coe
      MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_32
      (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W._%ˢ_
d__'37''738'__14 :: Integer -> Integer -> Integer
d__'37''738'__14
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__126 (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W._/ˢ_
d__'47''738'__16 :: Integer -> Integer -> Integer
d__'47''738'__16
  = coe
      MAlonzo.Code.Once.Word.d__'47''738'__120 (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W._<ˢ_
d__'60''738'__18 :: Integer -> Integer -> Bool
d__'60''738'__18
  = coe MAlonzo.Code.Once.Word.d__'60''738'__80 (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W._≡ʷ_
d__'8801''695'__20 :: Integer -> Integer -> Bool
d__'8801''695'__20 = coe MAlonzo.Code.Once.Word.du__'8801''695'__86
-- Once.Arith.SigOp.BlockSemBridge.W._⊕_
d__'8853'__22 :: Integer -> Integer -> Integer
d__'8853'__22
  = coe MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W._⊖_
d__'8854'__24 :: Integer -> Integer -> Integer
d__'8854'__24
  = coe MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W._⊗_
d__'8855'__26 :: Integer -> Integer -> Integer
d__'8855'__26
  = coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W.%ˢ-else
d_'37''738''45'else_28 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_28 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.%ˢ-in-range
d_'37''738''45'in'45'range_30 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_30 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_548
      (coe (64 :: Integer)) v2 v3 v4
-- Once.Arith.SigOp.BlockSemBridge.W.%ˢ-mid
d_'37''738''45'mid_32 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_32 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.%ˢ-negOne
d_'37''738''45'negOne_34 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_34 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.%ˢ-zero
d_'37''738''45'zero_36 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_36 = erased
-- Once.Arith.SigOp.BlockSemBridge.W./ˢ-else
d_'47''738''45'else_38 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_38 = erased
-- Once.Arith.SigOp.BlockSemBridge.W./ˢ-in-range
d_'47''738''45'in'45'range_40 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_40 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_514
      (coe (64 :: Integer)) v2 v3
-- Once.Arith.SigOp.BlockSemBridge.W./ˢ-mid
d_'47''738''45'mid_42 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_42 = erased
-- Once.Arith.SigOp.BlockSemBridge.W./ˢ-negOne
d_'47''738''45'negOne_44 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_44 = erased
-- Once.Arith.SigOp.BlockSemBridge.W./ˢ-pow2
d_'47''738''45'pow2_46 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_46 = erased
-- Once.Arith.SigOp.BlockSemBridge.W./ˢ-zero
d_'47''738''45'zero_48 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_48 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.0<half
d_0'60'half_50 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_50 = coe MAlonzo.Code.Once.Word.du_0'60'half_168
-- Once.Arith.SigOp.BlockSemBridge.W.0<modulus
d_0'60'modulus_52 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_52 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_166
-- Once.Arith.SigOp.BlockSemBridge.W.0<negOne
d_0'60'negOne_54 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_54 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_370 (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W.1<modulus
d_1'60'modulus_56 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_56
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_650 (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W.2*n≡n+n
d_2'42'n'8801'n'43'n_58 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_58 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.2≤modulus
d_2'8804'modulus_60 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_60 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_366 (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W.InRange
d_InRange_62 :: Integer -> ()
d_InRange_62 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.Word
d_Word_64 :: ()
d_Word_64 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.fromℤ
d_fromℤ_66 :: Integer -> Integer
d_fromℤ_66
  = coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W.fromℤ-0
d_fromℤ'45'0_68 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_68 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.fromℤ-in-range
d_fromℤ'45'in'45'range_70 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_70
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_174
      (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_72 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_72 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.fromℤ-neg1
d_fromℤ'45'neg1_74 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_74 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.half
d_half_76 :: Integer
d_half_76
  = coe MAlonzo.Code.Once.Word.d_half_48 (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W.half<modulus
d_half'60'modulus_78 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_78 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_374 (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W.half≡2^b
d_half'8801'2'94'b_80 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_80 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.half≤negOne
d_half'8804'negOne_82 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_82 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_394
      (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W.inRange?
d_inRange'63'_84 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_84
  = coe MAlonzo.Code.Once.Word.d_inRange'63'_62 (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W.intMin
d_intMin_86 :: Integer
d_intMin_86
  = coe MAlonzo.Code.Once.Word.d_intMin_54 (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W.modulus
d_modulus_88 :: Integer
d_modulus_88
  = coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_90 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_90 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.modulus≢0
d_modulus'8802'0_92 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_92
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W.mod∸half≡half
d_mod'8760'half'8801'half_94 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_94 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.mod≡half+half
d_mod'8801'half'43'half_96 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_96 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.negOne
d_negOne_98 :: Integer
d_negOne_98
  = coe MAlonzo.Code.Once.Word.d_negOne_78 (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W.negOne<modulus
d_negOne'60'modulus_100 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_100 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_382
      (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W.negOne≢0
d_negOne'8802'0_102 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_102 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.norm
d_norm_104 :: Integer -> Integer
d_norm_104
  = coe MAlonzo.Code.Once.Word.d_norm_16 (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W.norm-0
d_norm'45'0_106 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_106 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.norm-id
d_norm'45'id_108 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_108 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.sdiv2ᵏ
d_sdiv2'7503'_110 :: Integer -> Integer -> Integer
d_sdiv2'7503'_110
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_138 (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W.shlᵂ
d_shl'7490'_112 :: Integer -> Integer -> Integer
d_shl'7490'_112
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_132 (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W.sucNegOne≡mod
d_sucNegOne'8801'mod_114 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_114 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.tdiv-neg1
d_tdiv'45'neg1_116 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_116 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.tmod-neg1
d_tmod'45'neg1_118 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_118 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.toWord
d_toWord_120 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_120 v0 v1
  = coe MAlonzo.Code.Once.Word.du_toWord_68 (coe (64 :: Integer)) v0
-- Once.Arith.SigOp.BlockSemBridge.W.toWord≡fromℤ
d_toWord'8801'fromℤ_122 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'8801'fromℤ_122 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.toℤ
d_toℤ_124 :: Integer -> Integer
d_toℤ_124
  = coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W.toℤ-negOne
d_toℤ'45'negOne_126 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_126 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.≡ᵇ-refl
d_'8801''7495''45'refl_128 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_128 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.≡ᵇ0-false
d_'8801''7495'0'45'false_130 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_130 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_132 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_132 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.⊕-neg
d_'8853''45'neg_134 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_134 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.⊕-neg-suc
d_'8853''45'neg'45'suc_136 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_136 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.⊕-normʳ
d_'8853''45'norm'691'_138 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_138 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.⊕≡+
d_'8853''8801''43'_140 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_140 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.⊖-normʳ
d_'8854''45'norm'691'_142 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_142 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.⊖≡∸
d_'8854''8801''8760'_144 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_144 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.⊗-pow2
d_'8855''45'pow2_146 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_146 = erased
-- Once.Arith.SigOp.BlockSemBridge.W.⊝_
d_'8861'__148 :: Integer -> Integer
d_'8861'__148
  = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
-- Once.Arith.SigOp.BlockSemBridge.W.⊝-intMin
d_'8861''45'intMin_150 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_150 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_154 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_154
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'base'45'to'45'full_636
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_156 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_156 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_158 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_158 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_160 ::
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_160
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'full'45'to'45'base_600
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-functor
d_coerce'45'functor_162 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor_162 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_96 v0 v2
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_164 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_164 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_138
      v0 v2
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-round-trip
d_coerce'45'round'45'trip_166 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_166 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-struct
d_coerce'45'struct_168 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct_168
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct_268
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_170 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_170 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_172 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_172
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct'8315''185'_274
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_174 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_174 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-μ-in
d_coerce'45'μ'45'in_176 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_176 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'in_748 v0 v2
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-μ-out
d_coerce'45'μ'45'out_178 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_178 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_790 v0 v1
      v3
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_180 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_180 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_182 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_182 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-ν-in
d_coerce'45'ν'45'in_184 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_184
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_982
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-ν-out
d_coerce'45'ν'45'out_186 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_186
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'out_988
-- Once.Arith.SigOp.BlockSemBridge.M.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_188 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_188 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_190 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_190 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_192 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_192 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.fmap-struct-coherence
d_fmap'45'struct'45'coherence_194 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_194 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_196 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_196 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.sem-CoIn
d_sem'45'CoIn_198 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'CoIn_198
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoIn_1002
-- Once.Arith.SigOp.BlockSemBridge.M.sem-CoOut
d_sem'45'CoOut_200 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 -> AgdaAny
d_sem'45'CoOut_200
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoOut_992
-- Once.Arith.SigOp.BlockSemBridge.M.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_202 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_202 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.sem-In
d_sem'45'In_204 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_μS_182
d_sem'45'In_204
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'In_922
-- Once.Arith.SigOp.BlockSemBridge.M.sem-In-Out
d_sem'45'In'45'Out_206 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_206 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.sem-Out
d_sem'45'Out_208 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'Out_208
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'Out_930
-- Once.Arith.SigOp.BlockSemBridge.M.sem-Out-In
d_sem'45'Out'45'In_210 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_210 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.sem-ana
d_sem'45'ana_212 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'ana_212 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'ana_1026 v0 v2 v3
-- Once.Arith.SigOp.BlockSemBridge.M.sem-case
d_sem'45'case_214 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_214 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'case_332 v3 v4 v5
-- Once.Arith.SigOp.BlockSemBridge.M.sem-case-inl
d_sem'45'case'45'inl_216 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_216 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.sem-case-inr
d_sem'45'case'45'inr_218 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_218 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.sem-cata
d_sem'45'cata_220 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'cata_220 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_942 v0 v1 v3
-- Once.Arith.SigOp.BlockSemBridge.M.sem-cata-compute
d_sem'45'cata'45'compute_222 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_222 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.sem-fmap
d_sem'45'fmap_224 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_224 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_420 v0 v3 v4
-- Once.Arith.SigOp.BlockSemBridge.M.sem-fmap-Type
d_sem'45'fmap'45'Type_226 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_226 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap'45'Type_464 v0 v3
      v4
-- Once.Arith.SigOp.BlockSemBridge.M.sem-fst
d_sem'45'fst_228 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_228 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fst_296 v2
-- Once.Arith.SigOp.BlockSemBridge.M.sem-fst-pair
d_sem'45'fst'45'pair_230 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_230 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.sem-functor-coherence
d_sem'45'functor'45'coherence_232 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_232 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.sem-fuseNat
d_sem'45'fuseNat_234 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'fuseNat_234 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat_1156 v0 v1 v2
      v3 v5 v6
-- Once.Arith.SigOp.BlockSemBridge.M.sem-fuseNat-cong
d_sem'45'fuseNat'45'cong_236 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (() ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fuseNat'45'cong_236 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.sem-fuseNat-events
d_sem'45'fuseNat'45'events_238 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'fuseNat'45'events_238 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat'45'events_1252
      v1 v2 v3 v4 v5 v6 v8 v9
-- Once.Arith.SigOp.BlockSemBridge.M.sem-inl
d_sem'45'inl_240 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_240 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inl_318
-- Once.Arith.SigOp.BlockSemBridge.M.sem-inr
d_sem'45'inr_242 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_242 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inr_324
-- Once.Arith.SigOp.BlockSemBridge.M.sem-pair
d_sem'45'pair_244 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_244 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'pair_308 v2 v3
-- Once.Arith.SigOp.BlockSemBridge.M.sem-para
d_sem'45'para_246 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'para_246 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'para_958 v0 v1 v3 v4
-- Once.Arith.SigOp.BlockSemBridge.M.sem-snd
d_sem'45'snd_248 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_248 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'snd_302 v2
-- Once.Arith.SigOp.BlockSemBridge.M.sem-snd-pair
d_sem'45'snd'45'pair_250 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_250 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.sfmapSemAna
d_sfmapSemAna_252 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmapSemAna_252 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sfmapSemAna_1034 v0 v1 v3 v4
-- Once.Arith.SigOp.BlockSemBridge.M.sfmapSemAna-is-sfmap
d_sfmapSemAna'45'is'45'sfmap_254 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapSemAna'45'is'45'sfmap_254 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.⟦_⟧
d_'10214'_'10215'_256 :: MAlonzo.Code.Once.Type.T_Type_112 -> ()
d_'10214'_'10215'_256 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.⟦_⟧F
d_'10214'_'10215'F_258 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> ()
d_'10214'_'10215'F_258 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.⟦μ⟧
d_'10214'μ'10215'_260 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'μ'10215'_260 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.⟦ν⟧
d_'10214'ν'10215'_262 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'ν'10215'_262 = erased
-- Once.Arith.SigOp.BlockSemBridge.toWord
d_toWord_266 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny -> AgdaAny
d_toWord_266 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'unit_10
        -> coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12
        -> coe
             MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer)) (coe v1)
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_14 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_toWord_266 (coe v2) (coe v4))
                    (coe d_toWord_266 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.BlockSemBridge.project-commute
d_project'45'commute_284 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_project'45'commute_284 = erased
-- Once.Arith.SigOp.BlockSemBridge.ainput-leaf
d_ainput'45'leaf_328 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ainput'45'leaf_328 = erased
-- Once.Arith.SigOp.BlockSemBridge.eval≡semM
d_eval'8801'semM_360 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'8801'semM_360 = erased
