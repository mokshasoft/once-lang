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
import qualified MAlonzo.Code.Agda.Builtin.List
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
import qualified MAlonzo.Code.Once.Adequacy.MachineTrace
import qualified MAlonzo.Code.Once.Arith.Backend.CallAnswer
import qualified MAlonzo.Code.Once.Arith.Backend.RunTraceMachine
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Emit
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.RunTrace
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Spec.Float.Arith
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic
import qualified MAlonzo.Code.Once.Spec.Trace
import qualified MAlonzo.Code.Once.Spec.Word
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg
import qualified MAlonzo.Code.Once.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.CPU.X86-64.W._%ˢ_
d__'37''738'__10 :: Integer -> Integer -> Integer
d__'37''738'__10
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'37''738'__122 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W._/ˢ_
d__'47''738'__12 :: Integer -> Integer -> Integer
d__'47''738'__12
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'47''738'__116 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W._<ˢ_
d__'60''738'__14 :: Integer -> Integer -> Bool
d__'60''738'__14
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'60''738'__76 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W._divℕ_
d__divℕ__16 :: Integer -> Integer -> Integer
d__divℕ__16 = coe MAlonzo.Code.Once.Spec.Word.du__divℕ__88
-- Once.Adequacy.CPU.X86-64.W._modℕ_
d__modℕ__18 :: Integer -> Integer -> Integer
d__modℕ__18 = coe MAlonzo.Code.Once.Spec.Word.du__modℕ__90
-- Once.Adequacy.CPU.X86-64.W._≡ʷ_
d__'8801''695'__20 :: Integer -> Integer -> Bool
d__'8801''695'__20
  = coe MAlonzo.Code.Once.Spec.Word.du__'8801''695'__82
-- Once.Adequacy.CPU.X86-64.W._⊕_
d__'8853'__22 :: Integer -> Integer -> Integer
d__'8853'__22
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8853'__28 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W._⊖_
d__'8854'__24 :: Integer -> Integer -> Integer
d__'8854'__24
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8854'__34 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W._⊗_
d__'8855'__26 :: Integer -> Integer -> Integer
d__'8855'__26
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8855'__40 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.InRange
d_InRange_28 :: Integer -> ()
d_InRange_28 = erased
-- Once.Adequacy.CPU.X86-64.W.Word
d_Word_30 :: ()
d_Word_30 = erased
-- Once.Adequacy.CPU.X86-64.W.fromℤ
d_fromℤ_32 :: Integer -> Integer
d_fromℤ_32
  = coe MAlonzo.Code.Once.Spec.Word.d_fromℤ_22 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.half
d_half_34 :: Integer
d_half_34
  = coe MAlonzo.Code.Once.Spec.Word.d_half_50 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.inRange?
d_inRange'63'_36 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_36
  = coe
      MAlonzo.Code.Once.Spec.Word.d_inRange'63'_66 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.intMin
d_intMin_38 :: Integer
d_intMin_38
  = coe MAlonzo.Code.Once.Spec.Word.d_intMin_56 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.modulus
d_modulus_40 :: Integer
d_modulus_40
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.modulus≢0
d_modulus'8802'0_42 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_42
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus'8802'0_14
      (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.negOne
d_negOne_44 :: Integer
d_negOne_44
  = coe MAlonzo.Code.Once.Spec.Word.d_negOne_58 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.norm
d_norm_46 :: Integer -> Integer
d_norm_46
  = coe MAlonzo.Code.Once.Spec.Word.d_norm_18 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.tdivℤ
d_tdivℤ_48 :: Integer -> Integer -> Integer
d_tdivℤ_48 = coe MAlonzo.Code.Once.Spec.Word.du_tdivℤ_104
-- Once.Adequacy.CPU.X86-64.W.tmodℤ
d_tmodℤ_50 :: Integer -> Integer -> Integer
d_tmodℤ_50 = coe MAlonzo.Code.Once.Spec.Word.du_tmodℤ_106
-- Once.Adequacy.CPU.X86-64.W.toWord
d_toWord_52 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_52 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Word.du_toWord_72 (coe (64 :: Integer)) v0
-- Once.Adequacy.CPU.X86-64.W.toℤ
d_toℤ_54 :: Integer -> Integer
d_toℤ_54
  = coe MAlonzo.Code.Once.Spec.Word.d_toℤ_52 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.⊝_
d_'8861'__56 :: Integer -> Integer
d_'8861'__56
  = coe
      MAlonzo.Code.Once.Spec.Word.d_'8861'__46 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.WL.%ˢ-else
d_'37''738''45'else_60 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_60 = erased
-- Once.Adequacy.CPU.X86-64.WL.%ˢ-in-range
d_'37''738''45'in'45'range_62 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_62 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_530
      (coe (64 :: Integer)) v2 v3 v4
-- Once.Adequacy.CPU.X86-64.WL.%ˢ-mid
d_'37''738''45'mid_64 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_64 = erased
-- Once.Adequacy.CPU.X86-64.WL.%ˢ-negOne
d_'37''738''45'negOne_66 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_66 = erased
-- Once.Adequacy.CPU.X86-64.WL.%ˢ-zero
d_'37''738''45'zero_68 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_68 = erased
-- Once.Adequacy.CPU.X86-64.WL./ˢ-else
d_'47''738''45'else_70 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_70 = erased
-- Once.Adequacy.CPU.X86-64.WL./ˢ-in-range
d_'47''738''45'in'45'range_72 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_72 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_496
      (coe (64 :: Integer)) v2 v3
-- Once.Adequacy.CPU.X86-64.WL./ˢ-mid
d_'47''738''45'mid_74 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_74 = erased
-- Once.Adequacy.CPU.X86-64.WL./ˢ-negOne
d_'47''738''45'negOne_76 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_76 = erased
-- Once.Adequacy.CPU.X86-64.WL./ˢ-pow2
d_'47''738''45'pow2_78 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_78 = erased
-- Once.Adequacy.CPU.X86-64.WL./ˢ-zero
d_'47''738''45'zero_80 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_80 = erased
-- Once.Adequacy.CPU.X86-64.WL.0<half
d_0'60'half_82 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_82 = coe MAlonzo.Code.Once.Word.du_0'60'half_100
-- Once.Adequacy.CPU.X86-64.WL.0<modulus
d_0'60'modulus_84 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_84 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_98
-- Once.Adequacy.CPU.X86-64.WL.0<negOne
d_0'60'negOne_86 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_86 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_352 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.WL.1<modulus
d_1'60'modulus_88 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_88
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_722 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.WL.2*n≡n+n
d_2'42'n'8801'n'43'n_90 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_90 = erased
-- Once.Adequacy.CPU.X86-64.WL.2≤modulus
d_2'8804'modulus_92 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_92 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_348 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.WL.<⇒<ᵇtrue
d_'60''8658''60''7495'true_94 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8658''60''7495'true_94 = erased
-- Once.Adequacy.CPU.X86-64.WL.fromℤ-0
d_fromℤ'45'0_96 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_96 = erased
-- Once.Adequacy.CPU.X86-64.WL.fromℤ-in-range
d_fromℤ'45'in'45'range_98 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_98
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_106
      (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.WL.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_100 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_100 = erased
-- Once.Adequacy.CPU.X86-64.WL.fromℤ-neg1
d_fromℤ'45'neg1_102 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_102 = erased
-- Once.Adequacy.CPU.X86-64.WL.half<modulus
d_half'60'modulus_104 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_104 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_356 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.WL.half≡2^b
d_half'8801'2'94'b_106 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_106 = erased
-- Once.Adequacy.CPU.X86-64.WL.half≤negOne
d_half'8804'negOne_108 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_108 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_376
      (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.WL.lit-hi
d_lit'45'hi_110 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'hi_110 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Word.du_lit'45'hi_580 v3
-- Once.Adequacy.CPU.X86-64.WL.lit-lo
d_lit'45'lo_112 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'lo_112 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_lit'45'lo_592 (coe (64 :: Integer)) v2 v3
-- Once.Adequacy.CPU.X86-64.WL.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_114 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_114 = erased
-- Once.Adequacy.CPU.X86-64.WL.mod∸half≡half
d_mod'8760'half'8801'half_116 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_116 = erased
-- Once.Adequacy.CPU.X86-64.WL.mod≡half+half
d_mod'8801'half'43'half_118 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_118 = erased
-- Once.Adequacy.CPU.X86-64.WL.negOne<modulus
d_negOne'60'modulus_120 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_120 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_364
      (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.WL.negOne≢0
d_negOne'8802'0_122 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_122 = erased
-- Once.Adequacy.CPU.X86-64.WL.norm-0
d_norm'45'0_124 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_124 = erased
-- Once.Adequacy.CPU.X86-64.WL.norm-id
d_norm'45'id_126 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_126 = erased
-- Once.Adequacy.CPU.X86-64.WL.sbb-pos
d_sbb'45'pos_128 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sbb'45'pos_128 = erased
-- Once.Adequacy.CPU.X86-64.WL.sbb-zero
d_sbb'45'zero_130 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sbb'45'zero_130 = erased
-- Once.Adequacy.CPU.X86-64.WL.sdiv2ᵏ
d_sdiv2'7503'_132 :: Integer -> Integer -> Integer
d_sdiv2'7503'_132
  = coe MAlonzo.Code.Once.Word.d_sdiv2'7503'_70 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.WL.shlᵂ
d_shl'7490'_134 :: Integer -> Integer -> Integer
d_shl'7490'_134
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_64 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.WL.sucNegOne≡mod
d_sucNegOne'8801'mod_136 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_136 = erased
-- Once.Adequacy.CPU.X86-64.WL.tdiv-neg1
d_tdiv'45'neg1_138 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_138 = erased
-- Once.Adequacy.CPU.X86-64.WL.tmod-neg1
d_tmod'45'neg1_140 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_140 = erased
-- Once.Adequacy.CPU.X86-64.WL.toWord≡fromℤ
d_toWord'8801'fromℤ_142 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'8801'fromℤ_142 = erased
-- Once.Adequacy.CPU.X86-64.WL.toℤ-negOne
d_toℤ'45'negOne_144 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_144 = erased
-- Once.Adequacy.CPU.X86-64.WL.toℤ∘fromℤ
d_toℤ'8728'fromℤ_146 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'8728'fromℤ_146 = erased
-- Once.Adequacy.CPU.X86-64.WL.unplus
d_unplus_148 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_unplus_148 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Word.du_unplus_574 v4
-- Once.Adequacy.CPU.X86-64.WL.≡ᵇ0-false
d_'8801''7495'0'45'false_150 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_150 = erased
-- Once.Adequacy.CPU.X86-64.WL.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_152 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_152 = erased
-- Once.Adequacy.CPU.X86-64.WL.⊕-neg
d_'8853''45'neg_154 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_154 = erased
-- Once.Adequacy.CPU.X86-64.WL.⊕-neg-suc
d_'8853''45'neg'45'suc_156 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_156 = erased
-- Once.Adequacy.CPU.X86-64.WL.⊕-normʳ
d_'8853''45'norm'691'_158 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_158 = erased
-- Once.Adequacy.CPU.X86-64.WL.⊕≡+
d_'8853''8801''43'_160 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_160 = erased
-- Once.Adequacy.CPU.X86-64.WL.⊖-normʳ
d_'8854''45'norm'691'_162 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_162 = erased
-- Once.Adequacy.CPU.X86-64.WL.⊖-self
d_'8854''45'self_164 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'self_164 = erased
-- Once.Adequacy.CPU.X86-64.WL.⊖≡∸
d_'8854''8801''8760'_166 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_166 = erased
-- Once.Adequacy.CPU.X86-64.WL.⊗-pow2
d_'8855''45'pow2_168 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_168 = erased
-- Once.Adequacy.CPU.X86-64.WL.⊝-fromℤ
d_'8861''45'fromℤ_170 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'fromℤ_170 = erased
-- Once.Adequacy.CPU.X86-64.WL.⊝-intMin
d_'8861''45'intMin_172 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_172 = erased
-- Once.Adequacy.CPU.X86-64.WL.⊝-invol-norm
d_'8861''45'invol'45'norm_174 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'invol'45'norm_174 = erased
-- Once.Adequacy.CPU.X86-64.rd
d_rd_176 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 -> Integer
d_rd_176 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_248
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_396
         (coe v0))
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Emit.d_arith'45'reg_10
         (coe v1))
-- Once.Adequacy.CPU.X86-64.def
d_def_182 :: Maybe Integer -> Integer
d_def_182 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.X86-64.scratch-addr
d_scratch'45'addr_186 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer
d_scratch'45'addr_186 v0 v1
  = coe
      addInt
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_248
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_396
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
      (coe
         mulInt (coe (8 :: Integer))
         (coe
            MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.d_slot_20 (coe v1)))
-- Once.Adequacy.CPU.X86-64.side-off
d_side'45'off_192 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24 -> Integer
d_side'45'off_192 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_26
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_28
        -> coe (8 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.X86-64.path-load-go
d_path'45'load'45'go_194 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer
d_path'45'load'45'go_194 v0 v1 v2
  = case coe v2 of
      []
        -> coe
             d_def_182
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readMem_352
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_398
                   (coe v0))
                (coe v1))
      (:) v3 v4
        -> coe
             d_path'45'load'45'go_194 (coe v0)
             (coe
                d_def_182
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readMem_352
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_398
                      (coe v0))
                   (coe addInt (coe d_side'45'off_192 (coe v3)) (coe v1))))
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.X86-64.path-load
d_path'45'load_208 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer
d_path'45'load_208 v0 v1
  = coe
      d_path'45'load'45'go_194 (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_248
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_396
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20))
      (coe v1)
-- Once.Adequacy.CPU.X86-64.val-x86-64
d_val'45'x86'45'64_214 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer
d_val'45'x86'45'64_214 v0 v1 ~v2 = du_val'45'x86'45'64_214 v0 v1
du_val'45'x86'45'64_214 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  Integer
du_val'45'x86'45'64_214 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'imm_26 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Word.d_fromℤ_22 (coe (64 :: Integer))
             (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_28 v2 v3
        -> coe d_rd_176 (coe v1) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'r'45'm_30 v2 v3
        -> coe d_rd_176 (coe v1) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'm'45'r_32 v2 v3
        -> coe
             d_def_182
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readMem_352
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_398
                   (coe v1))
                (coe d_scratch'45'addr_186 (coe v1) (coe v3)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'arg_34 v2 v3
        -> coe d_path'45'load_208 (coe v1) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xadd'45'rr_36 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Word.d__'8853'__28 (coe (64 :: Integer))
             (coe d_rd_176 (coe v1) (coe v2)) (coe d_rd_176 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsub'45'rr_38 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Word.d__'8854'__34 (coe (64 :: Integer))
             (coe d_rd_176 (coe v1) (coe v2)) (coe d_rd_176 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Ximul'45'rr_40 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Word.d__'8855'__40 (coe (64 :: Integer))
             (coe d_rd_176 (coe v1) (coe v2)) (coe d_rd_176 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xneg'45'r_42 v2
        -> coe
             MAlonzo.Code.Once.Spec.Word.d_'8861'__46 (coe (64 :: Integer))
             (coe d_rd_176 (coe v1) (coe v2))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'rrr_44 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Word.d__'47''738'__116 (coe (64 :: Integer))
             (coe d_rd_176 (coe v1) (coe v3)) (coe d_rd_176 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'rrr_46 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Word.d__'37''738'__122 (coe (64 :: Integer))
             (coe d_rd_176 (coe v1) (coe v3)) (coe d_rd_176 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xcmp'45'rrr_48 v2 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Arith.CmpOp.d_cmp'45'bit_62 (coe (64 :: Integer))
             (coe v2) (coe d_rd_176 (coe v1) (coe v4))
             (coe d_rd_176 (coe v1) (coe v5))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'safe'45'rrr_50 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Word.d__'47''738'__116 (coe (64 :: Integer))
             (coe d_rd_176 (coe v1) (coe v3)) (coe d_rd_176 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'safe'45'rrr_52 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Word.d__'37''738'__122 (coe (64 :: Integer))
             (coe d_rd_176 (coe v1) (coe v3)) (coe d_rd_176 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xshl'45'rri_54 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d_shl'7490'_64 (coe (64 :: Integer))
             (coe d_rd_176 (coe v1) (coe v3)) (coe v4)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsdiv'45'pow2'45'rri_56 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d_sdiv2'7503'_70 (coe (64 :: Integer))
             (coe d_rd_176 (coe v1) (coe v3)) (coe v4)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfadd'45'rr_58 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Float.Arith.d_fadd_316
             (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_binary64_44)
             (coe d_rd_176 (coe v1) (coe v2)) (coe d_rd_176 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsub'45'rr_60 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Float.Arith.d_fsub_318
             (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_binary64_44)
             (coe d_rd_176 (coe v1) (coe v2)) (coe d_rd_176 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfmul'45'rr_62 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Float.Arith.d_fmul_320
             (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_binary64_44)
             (coe d_rd_176 (coe v1) (coe v2)) (coe d_rd_176 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfdiv'45'rrr_64 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Float.Arith.d_fdiv_322
             (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_binary64_44)
             (coe d_rd_176 (coe v1) (coe v3)) (coe d_rd_176 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsubr'45'rr_66 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Float.Arith.d_fsub_318
             (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_binary64_44)
             (coe d_rd_176 (coe v1) (coe v3)) (coe d_rd_176 (coe v1) (coe v2))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfneg'45'r_68 v2
        -> coe
             MAlonzo.Code.Once.Spec.Float.Arith.d_fneg_358
             (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_binary64_44)
             (coe d_rd_176 (coe v1) (coe v2))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xi2f'45'r_70 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Float.Arith.d_i2f_364
             (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_binary64_44)
             (coe
                MAlonzo.Code.Once.Spec.Word.d_toℤ_52 (coe (64 :: Integer))
                (coe d_rd_176 (coe v1) (coe v3)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'fimm_72 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Float.Decimal.d_round_176
             (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_binary64_44) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'farg_74 v2 v3
        -> coe d_path'45'load_208 (coe v1) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'out_76 v2
        -> coe d_rd_176 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.X86-64.ev-x86-64
d_ev'45'x86'45'64_384
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-64.ev-x86-64"
-- Once.Adequacy.CPU.X86-64.call-at-x86-64
d_call'45'at'45'x86'45'64_386
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-64.call-at-x86-64"
-- Once.Adequacy.CPU.X86-64.block-env
d_block'45'env_388 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'env_388 v0 v1
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
                    (coe d_block'45'env_388 (coe v3) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.X86-64.run-trace-x86-64
d_run'45'trace'45'x86'45'64_398 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.T_Image_12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18
d_run'45'trace'45'x86'45'64_398 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.MachineTrace.du_trace_80
      (coe
         MAlonzo.Code.Once.Arith.Backend.RunTraceMachine.du_δ_92
         (coe
            (\ v3 ->
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_404
                 (coe v3)))
         (coe
            (\ v3 ->
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_402
                 (coe v3)))
         (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_fetch_778)
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_execInstr_510)
         (coe
            MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.RunTrace.d_matchCall_10)
         (coe
            MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.RunTrace.d_ret'45'call_26
            (coe
               MAlonzo.Code.Once.Arith.Backend.CallAnswer.du_answer'45'at_158
               (coe v0) (coe d_call'45'at'45'x86'45'64_386)))
         (coe
            MAlonzo.Code.Data.Product.Base.du_uncurry_244
            (\ v3 v4 v5 ->
               coe
                 MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
                 (\ v6 v7 v8 -> coe du_val'45'x86'45'64_214 v6 v7) v3 v5))
         (coe d_ev'45'x86'45'64_384)
         (coe
            d_block'45'env_388
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.d_blocks_26 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.d_code_22 (coe v1)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v2))
-- Once.Adequacy.CPU.X86-64.decode-x86-64
d_decode'45'x86'45'64_406
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-64.decode-x86-64"
-- Once.Adequacy.CPU.X86-64.assemble-x86-64
d_assemble'45'x86'45'64_408
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-64.assemble-x86-64"
-- Once.Adequacy.CPU.X86-64.as-faithful-x86-64
d_as'45'faithful'45'x86'45'64_412
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-64.as-faithful-x86-64"
-- Once.Adequacy.CPU.X86-64.arch-semantics
d_arch'45'semantics_414 ::
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10
d_arch'45'semantics_414
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.Interface.C_constructor_90
      (\ v0 ->
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_initStateAt_418
           (coe
              MAlonzo.Code.Data.Maybe.Base.du_fromMaybe_46 (0 :: Integer)
              (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.d_entry_24 (coe v0))))
      (\ v0 ->
         coe
           MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_run_822
           (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.d_code_22 (coe v0)))
      d_run'45'trace'45'x86'45'64_398 d_decode'45'x86'45'64_406
      d_assemble'45'x86'45'64_408
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.d_print_84 (\ v0 -> v0)
