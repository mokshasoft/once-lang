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

module MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z64 where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Adequacy.CPU.Interface
import qualified MAlonzo.Code.Once.Arith.Backend.CallAnswer
import qualified MAlonzo.Code.Once.Arith.Backend.RunTraceCore
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Emit
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.RunTrace
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics
import qualified MAlonzo.Code.Once.Denotation.Behavior
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Float.Arith
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg
import qualified MAlonzo.Code.Once.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.CPU.X86-64.W._%ˢ_
d__'37''738'__10 :: Integer -> Integer -> Integer
d__'37''738'__10
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__126 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W._/ˢ_
d__'47''738'__12 :: Integer -> Integer -> Integer
d__'47''738'__12
  = coe
      MAlonzo.Code.Once.Word.d__'47''738'__120 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W._<ˢ_
d__'60''738'__14 :: Integer -> Integer -> Bool
d__'60''738'__14
  = coe MAlonzo.Code.Once.Word.d__'60''738'__80 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W._≡ʷ_
d__'8801''695'__16 :: Integer -> Integer -> Bool
d__'8801''695'__16 = coe MAlonzo.Code.Once.Word.du__'8801''695'__86
-- Once.Adequacy.CPU.X86-64.W._⊕_
d__'8853'__18 :: Integer -> Integer -> Integer
d__'8853'__18
  = coe MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W._⊖_
d__'8854'__20 :: Integer -> Integer -> Integer
d__'8854'__20
  = coe MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W._⊗_
d__'8855'__22 :: Integer -> Integer -> Integer
d__'8855'__22
  = coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.%ˢ-else
d_'37''738''45'else_24 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_24 = erased
-- Once.Adequacy.CPU.X86-64.W.%ˢ-in-range
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
      (coe (64 :: Integer)) v2 v3 v4
-- Once.Adequacy.CPU.X86-64.W.%ˢ-mid
d_'37''738''45'mid_28 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_28 = erased
-- Once.Adequacy.CPU.X86-64.W.%ˢ-negOne
d_'37''738''45'negOne_30 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_30 = erased
-- Once.Adequacy.CPU.X86-64.W.%ˢ-zero
d_'37''738''45'zero_32 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_32 = erased
-- Once.Adequacy.CPU.X86-64.W./ˢ-else
d_'47''738''45'else_34 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_34 = erased
-- Once.Adequacy.CPU.X86-64.W./ˢ-in-range
d_'47''738''45'in'45'range_36 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_36 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_570
      (coe (64 :: Integer)) v2 v3
-- Once.Adequacy.CPU.X86-64.W./ˢ-mid
d_'47''738''45'mid_38 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_38 = erased
-- Once.Adequacy.CPU.X86-64.W./ˢ-negOne
d_'47''738''45'negOne_40 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_40 = erased
-- Once.Adequacy.CPU.X86-64.W./ˢ-pow2
d_'47''738''45'pow2_42 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_42 = erased
-- Once.Adequacy.CPU.X86-64.W./ˢ-zero
d_'47''738''45'zero_44 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_44 = erased
-- Once.Adequacy.CPU.X86-64.W.0<half
d_0'60'half_46 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_46 = coe MAlonzo.Code.Once.Word.du_0'60'half_168
-- Once.Adequacy.CPU.X86-64.W.0<modulus
d_0'60'modulus_48 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_48 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_166
-- Once.Adequacy.CPU.X86-64.W.0<negOne
d_0'60'negOne_50 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_50 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_426 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.1<modulus
d_1'60'modulus_52 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_52
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_796 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.2*n≡n+n
d_2'42'n'8801'n'43'n_54 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_54 = erased
-- Once.Adequacy.CPU.X86-64.W.2≤modulus
d_2'8804'modulus_56 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_56 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_422 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.<⇒<ᵇtrue
d_'60''8658''60''7495'true_58 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8658''60''7495'true_58 = erased
-- Once.Adequacy.CPU.X86-64.W.InRange
d_InRange_60 :: Integer -> ()
d_InRange_60 = erased
-- Once.Adequacy.CPU.X86-64.W.Word
d_Word_62 :: ()
d_Word_62 = erased
-- Once.Adequacy.CPU.X86-64.W.fromℤ
d_fromℤ_64 :: Integer -> Integer
d_fromℤ_64
  = coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.fromℤ-0
d_fromℤ'45'0_66 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_66 = erased
-- Once.Adequacy.CPU.X86-64.W.fromℤ-in-range
d_fromℤ'45'in'45'range_68 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_68
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_174
      (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_70 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_70 = erased
-- Once.Adequacy.CPU.X86-64.W.fromℤ-neg1
d_fromℤ'45'neg1_72 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_72 = erased
-- Once.Adequacy.CPU.X86-64.W.half
d_half_74 :: Integer
d_half_74
  = coe MAlonzo.Code.Once.Word.d_half_48 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.half<modulus
d_half'60'modulus_76 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_76 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_430 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.half≡2^b
d_half'8801'2'94'b_78 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_78 = erased
-- Once.Adequacy.CPU.X86-64.W.half≤negOne
d_half'8804'negOne_80 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_80 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_450
      (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.inRange?
d_inRange'63'_82 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_82
  = coe MAlonzo.Code.Once.Word.d_inRange'63'_62 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.intMin
d_intMin_84 :: Integer
d_intMin_84
  = coe MAlonzo.Code.Once.Word.d_intMin_54 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.lit-hi
d_lit'45'hi_86 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'hi_86 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Word.du_lit'45'hi_654 v3
-- Once.Adequacy.CPU.X86-64.W.lit-lo
d_lit'45'lo_88 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'lo_88 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_lit'45'lo_666 (coe (64 :: Integer)) v2 v3
-- Once.Adequacy.CPU.X86-64.W.modulus
d_modulus_90 :: Integer
d_modulus_90
  = coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_92 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_92 = erased
-- Once.Adequacy.CPU.X86-64.W.modulus≢0
d_modulus'8802'0_94 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_94
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.mod∸half≡half
d_mod'8760'half'8801'half_96 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_96 = erased
-- Once.Adequacy.CPU.X86-64.W.mod≡half+half
d_mod'8801'half'43'half_98 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_98 = erased
-- Once.Adequacy.CPU.X86-64.W.negOne
d_negOne_100 :: Integer
d_negOne_100
  = coe MAlonzo.Code.Once.Word.d_negOne_78 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.negOne<modulus
d_negOne'60'modulus_102 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_102 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_438
      (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.negOne≢0
d_negOne'8802'0_104 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_104 = erased
-- Once.Adequacy.CPU.X86-64.W.norm
d_norm_106 :: Integer -> Integer
d_norm_106
  = coe MAlonzo.Code.Once.Word.d_norm_16 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.norm-0
d_norm'45'0_108 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_108 = erased
-- Once.Adequacy.CPU.X86-64.W.norm-id
d_norm'45'id_110 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_110 = erased
-- Once.Adequacy.CPU.X86-64.W.sbb-pos
d_sbb'45'pos_112 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sbb'45'pos_112 = erased
-- Once.Adequacy.CPU.X86-64.W.sbb-zero
d_sbb'45'zero_114 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sbb'45'zero_114 = erased
-- Once.Adequacy.CPU.X86-64.W.sdiv2ᵏ
d_sdiv2'7503'_116 :: Integer -> Integer -> Integer
d_sdiv2'7503'_116
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_138 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.shlᵂ
d_shl'7490'_118 :: Integer -> Integer -> Integer
d_shl'7490'_118
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_132 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.sucNegOne≡mod
d_sucNegOne'8801'mod_120 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_120 = erased
-- Once.Adequacy.CPU.X86-64.W.tdiv-neg1
d_tdiv'45'neg1_122 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_122 = erased
-- Once.Adequacy.CPU.X86-64.W.tmod-neg1
d_tmod'45'neg1_124 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_124 = erased
-- Once.Adequacy.CPU.X86-64.W.toWord
d_toWord_126 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_126 v0 v1
  = coe MAlonzo.Code.Once.Word.du_toWord_68 (coe (64 :: Integer)) v0
-- Once.Adequacy.CPU.X86-64.W.toWord≡fromℤ
d_toWord'8801'fromℤ_128 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'8801'fromℤ_128 = erased
-- Once.Adequacy.CPU.X86-64.W.toℤ
d_toℤ_130 :: Integer -> Integer
d_toℤ_130
  = coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.toℤ-negOne
d_toℤ'45'negOne_132 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_132 = erased
-- Once.Adequacy.CPU.X86-64.W.toℤ∘fromℤ
d_toℤ'8728'fromℤ_134 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'8728'fromℤ_134 = erased
-- Once.Adequacy.CPU.X86-64.W.unplus
d_unplus_136 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_unplus_136 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Word.du_unplus_648 v4
-- Once.Adequacy.CPU.X86-64.W.≡ᵇ-refl
d_'8801''7495''45'refl_138 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_138 = erased
-- Once.Adequacy.CPU.X86-64.W.≡ᵇ0-false
d_'8801''7495'0'45'false_140 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_140 = erased
-- Once.Adequacy.CPU.X86-64.W.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_142 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_142 = erased
-- Once.Adequacy.CPU.X86-64.W.⊕-neg
d_'8853''45'neg_144 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_144 = erased
-- Once.Adequacy.CPU.X86-64.W.⊕-neg-suc
d_'8853''45'neg'45'suc_146 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_146 = erased
-- Once.Adequacy.CPU.X86-64.W.⊕-normʳ
d_'8853''45'norm'691'_148 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_148 = erased
-- Once.Adequacy.CPU.X86-64.W.⊕≡+
d_'8853''8801''43'_150 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_150 = erased
-- Once.Adequacy.CPU.X86-64.W.⊖-normʳ
d_'8854''45'norm'691'_152 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_152 = erased
-- Once.Adequacy.CPU.X86-64.W.⊖-self
d_'8854''45'self_154 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'self_154 = erased
-- Once.Adequacy.CPU.X86-64.W.⊖≡∸
d_'8854''8801''8760'_156 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_156 = erased
-- Once.Adequacy.CPU.X86-64.W.⊗-pow2
d_'8855''45'pow2_158 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_158 = erased
-- Once.Adequacy.CPU.X86-64.W.⊝_
d_'8861'__160 :: Integer -> Integer
d_'8861'__160
  = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.⊝-fromℤ
d_'8861''45'fromℤ_162 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'fromℤ_162 = erased
-- Once.Adequacy.CPU.X86-64.W.⊝-intMin
d_'8861''45'intMin_164 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_164 = erased
-- Once.Adequacy.CPU.X86-64.W.⊝-invol-norm
d_'8861''45'invol'45'norm_166 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'invol'45'norm_166 = erased
-- Once.Adequacy.CPU.X86-64.rd
d_rd_168 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 -> Integer
d_rd_168 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_240
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_388
         (coe v0))
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Emit.d_arith'45'reg_10
         (coe v1))
-- Once.Adequacy.CPU.X86-64.def
d_def_174 :: Maybe Integer -> Integer
d_def_174 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.X86-64.scratch-addr
d_scratch'45'addr_178 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer
d_scratch'45'addr_178 v0 v1
  = coe
      addInt
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_240
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_388
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
      (coe
         mulInt (coe (8 :: Integer))
         (coe
            MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.d_slot_20 (coe v1)))
-- Once.Adequacy.CPU.X86-64.side-off
d_side'45'off_184 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24 -> Integer
d_side'45'off_184 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_26
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_28
        -> coe (8 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.X86-64.path-load-go
d_path'45'load'45'go_186 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer
d_path'45'load'45'go_186 v0 v1 v2
  = case coe v2 of
      []
        -> coe
             d_def_174
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readMem_344
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_390
                   (coe v0))
                (coe v1))
      (:) v3 v4
        -> coe
             d_path'45'load'45'go_186 (coe v0)
             (coe
                d_def_174
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readMem_344
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_390
                      (coe v0))
                   (coe addInt (coe d_side'45'off_184 (coe v3)) (coe v1))))
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.X86-64.path-load
d_path'45'load_200 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer
d_path'45'load_200 v0 v1
  = coe
      d_path'45'load'45'go_186 (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_240
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_388
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20))
      (coe v1)
-- Once.Adequacy.CPU.X86-64.val-x86-64
d_val'45'x86'45'64_206 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer
d_val'45'x86'45'64_206 v0 v1 ~v2 = du_val'45'x86'45'64_206 v0 v1
du_val'45'x86'45'64_206 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  Integer
du_val'45'x86'45'64_206 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'imm_26 v2 v3
        -> coe
             MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer)) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_28 v2 v3
        -> coe d_rd_168 (coe v1) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'r'45'm_30 v2 v3
        -> coe d_rd_168 (coe v1) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'm'45'r_32 v2 v3
        -> coe
             d_def_174
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readMem_344
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_390
                   (coe v1))
                (coe d_scratch'45'addr_178 (coe v1) (coe v3)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'arg_34 v2 v3
        -> coe d_path'45'load_200 (coe v1) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xadd'45'rr_36 v2 v3
        -> coe
             MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer))
             (coe d_rd_168 (coe v1) (coe v2)) (coe d_rd_168 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsub'45'rr_38 v2 v3
        -> coe
             MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
             (coe d_rd_168 (coe v1) (coe v2)) (coe d_rd_168 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Ximul'45'rr_40 v2 v3
        -> coe
             MAlonzo.Code.Once.Word.d__'8855'__38 (coe (64 :: Integer))
             (coe d_rd_168 (coe v1) (coe v2)) (coe d_rd_168 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xneg'45'r_42 v2
        -> coe
             MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
             (coe d_rd_168 (coe v1) (coe v2))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'rrr_44 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'47''738'__120 (coe (64 :: Integer))
             (coe d_rd_168 (coe v1) (coe v3)) (coe d_rd_168 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'rrr_46 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'37''738'__126 (coe (64 :: Integer))
             (coe d_rd_168 (coe v1) (coe v3)) (coe d_rd_168 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xcmp'45'rrr_48 v2 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Arith.CmpOp.d_cmp'45'bit_62 (coe (64 :: Integer))
             (coe v2) (coe d_rd_168 (coe v1) (coe v4))
             (coe d_rd_168 (coe v1) (coe v5))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'safe'45'rrr_50 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'47''738'__120 (coe (64 :: Integer))
             (coe d_rd_168 (coe v1) (coe v3)) (coe d_rd_168 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'safe'45'rrr_52 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'37''738'__126 (coe (64 :: Integer))
             (coe d_rd_168 (coe v1) (coe v3)) (coe d_rd_168 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xshl'45'rri_54 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d_shl'7490'_132 (coe (64 :: Integer))
             (coe d_rd_168 (coe v1) (coe v3)) (coe v4)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsdiv'45'pow2'45'rri_56 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d_sdiv2'7503'_138 (coe (64 :: Integer))
             (coe d_rd_168 (coe v1) (coe v3)) (coe v4)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfadd'45'rr_58 v2 v3
        -> coe
             MAlonzo.Code.Once.Float.Arith.d_fadd_314
             (coe MAlonzo.Code.Once.Float.Dyadic.d_binary64_42)
             (coe d_rd_168 (coe v1) (coe v2)) (coe d_rd_168 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsub'45'rr_60 v2 v3
        -> coe
             MAlonzo.Code.Once.Float.Arith.d_fsub_316
             (coe MAlonzo.Code.Once.Float.Dyadic.d_binary64_42)
             (coe d_rd_168 (coe v1) (coe v2)) (coe d_rd_168 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfmul'45'rr_62 v2 v3
        -> coe
             MAlonzo.Code.Once.Float.Arith.d_fmul_318
             (coe MAlonzo.Code.Once.Float.Dyadic.d_binary64_42)
             (coe d_rd_168 (coe v1) (coe v2)) (coe d_rd_168 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfdiv'45'rrr_64 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Float.Arith.d_fdiv_320
             (coe MAlonzo.Code.Once.Float.Dyadic.d_binary64_42)
             (coe d_rd_168 (coe v1) (coe v3)) (coe d_rd_168 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsubr'45'rr_66 v2 v3
        -> coe
             MAlonzo.Code.Once.Float.Arith.d_fsub_316
             (coe MAlonzo.Code.Once.Float.Dyadic.d_binary64_42)
             (coe d_rd_168 (coe v1) (coe v3)) (coe d_rd_168 (coe v1) (coe v2))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfneg'45'r_68 v2
        -> coe
             MAlonzo.Code.Once.Float.Arith.d_fneg_356
             (coe MAlonzo.Code.Once.Float.Dyadic.d_binary64_42)
             (coe d_rd_168 (coe v1) (coe v2))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xi2f'45'r_70 v2 v3
        -> coe
             MAlonzo.Code.Once.Float.Arith.d_i2f_362
             (coe MAlonzo.Code.Once.Float.Dyadic.d_binary64_42)
             (coe
                MAlonzo.Code.Once.Word.d_toℤ_50 (coe (64 :: Integer))
                (coe d_rd_168 (coe v1) (coe v3)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'fimm_72 v2 v3
        -> coe
             MAlonzo.Code.Once.Float.Decimal.d_round_174
             (coe MAlonzo.Code.Once.Float.Dyadic.d_binary64_42) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'farg_74 v2 v3
        -> coe d_path'45'load_200 (coe v1) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'out_76 v2
        -> coe d_rd_168 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.X86-64.step-budget-x86-64
d_step'45'budget'45'x86'45'64_376
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-64.step-budget-x86-64"
-- Once.Adequacy.CPU.X86-64.ev-x86-64
d_ev'45'x86'45'64_378
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-64.ev-x86-64"
-- Once.Adequacy.CPU.X86-64.call-at-x86-64
d_call'45'at'45'x86'45'64_380
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-64.call-at-x86-64"
-- Once.Adequacy.CPU.X86-64.block-env
d_block'45'env_382 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'env_382 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe
                       MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v4)
                       (coe v1))
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5))
                    (coe d_block'45'env_382 (coe v3) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.X86-64.step-budget-x86-64-adequate
d_step'45'budget'45'x86'45'64'45'adequate_400
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-64.step-budget-x86-64-adequate"
-- Once.Adequacy.CPU.X86-64.run-trace-x86-64
d_run'45'trace'45'x86'45'64_402 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.T_Image_12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_run'45'trace'45'x86'45'64_402 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'trace_234
      (coe
         (\ v3 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_396
              (coe v3)))
      (coe
         (\ v3 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_394
              (coe v3)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_fetch_770)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_execInstr_502)
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.RunTrace.d_matchCall_10)
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.RunTrace.d_ret'45'call_18
         (coe
            MAlonzo.Code.Once.Arith.Backend.CallAnswer.du_answer'45'at_220
            (coe v0) (coe d_call'45'at'45'x86'45'64_380)))
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
              (\ v6 v7 v8 -> coe du_val'45'x86'45'64_206 v6 v7) v3 v5))
      (coe
         d_step'45'budget'45'x86'45'64_376
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.d_blocks_26 (coe v1))
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.d_code_22 (coe v1))
         v2)
      (coe d_ev'45'x86'45'64_378)
      (coe
         d_block'45'env_382
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.d_blocks_26 (coe v1)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.d_code_22 (coe v1))
      (coe v2)
      (coe
         d_step'45'budget'45'x86'45'64'45'adequate_400 v0
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.d_blocks_26 (coe v1))
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.d_code_22 (coe v1))
         v2)
-- Once.Adequacy.CPU.X86-64.decode-x86-64
d_decode'45'x86'45'64_410
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-64.decode-x86-64"
-- Once.Adequacy.CPU.X86-64.assemble-x86-64
d_assemble'45'x86'45'64_412
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-64.assemble-x86-64"
-- Once.Adequacy.CPU.X86-64.as-faithful-x86-64
d_as'45'faithful'45'x86'45'64_416
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-64.as-faithful-x86-64"
-- Once.Adequacy.CPU.X86-64.arch-semantics
d_arch'45'semantics_418 ::
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10
d_arch'45'semantics_418
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.Interface.C_constructor_90
      (\ v0 ->
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_initStateAt_410
           (coe
              MAlonzo.Code.Data.Maybe.Base.du_fromMaybe_46 (0 :: Integer)
              (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.d_entry_24 (coe v0))))
      (\ v0 ->
         coe
           MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_run_814
           (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.d_code_22 (coe v0)))
      d_run'45'trace'45'x86'45'64_402 d_decode'45'x86'45'64_410
      d_assemble'45'x86'45'64_412
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.d_print_78 (\ v0 -> v0)
