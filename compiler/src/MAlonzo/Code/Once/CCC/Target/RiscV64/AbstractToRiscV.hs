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

module MAlonzo.Code.Once.CCC.Target.RiscV64.AbstractToRiscV where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Target.RiscV64.PhysReg
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW._%ˢ_
d__'37''738'__12 :: Integer -> Integer -> Integer
d__'37''738'__12
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__126 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW._/ˢ_
d__'47''738'__14 :: Integer -> Integer -> Integer
d__'47''738'__14
  = coe
      MAlonzo.Code.Once.Word.d__'47''738'__120 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW._<ˢ_
d__'60''738'__16 :: Integer -> Integer -> Bool
d__'60''738'__16
  = coe MAlonzo.Code.Once.Word.d__'60''738'__80 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW._≡ʷ_
d__'8801''695'__18 :: Integer -> Integer -> Bool
d__'8801''695'__18 = coe MAlonzo.Code.Once.Word.du__'8801''695'__86
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW._⊕_
d__'8853'__20 :: Integer -> Integer -> Integer
d__'8853'__20
  = coe MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW._⊖_
d__'8854'__22 :: Integer -> Integer -> Integer
d__'8854'__22
  = coe MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW._⊗_
d__'8855'__24 :: Integer -> Integer -> Integer
d__'8855'__24
  = coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.%ˢ-else
d_'37''738''45'else_26 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_26 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.%ˢ-in-range
d_'37''738''45'in'45'range_28 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_28 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_604
      (coe (64 :: Integer)) v2 v3 v4
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.%ˢ-mid
d_'37''738''45'mid_30 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_30 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.%ˢ-negOne
d_'37''738''45'negOne_32 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_32 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.%ˢ-zero
d_'37''738''45'zero_34 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_34 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW./ˢ-else
d_'47''738''45'else_36 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_36 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW./ˢ-in-range
d_'47''738''45'in'45'range_38 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_38 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_570
      (coe (64 :: Integer)) v2 v3
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW./ˢ-mid
d_'47''738''45'mid_40 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_40 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW./ˢ-negOne
d_'47''738''45'negOne_42 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_42 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW./ˢ-pow2
d_'47''738''45'pow2_44 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_44 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW./ˢ-zero
d_'47''738''45'zero_46 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_46 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.0<half
d_0'60'half_48 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_48 = coe MAlonzo.Code.Once.Word.du_0'60'half_168
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.0<modulus
d_0'60'modulus_50 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_50 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_166
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.0<negOne
d_0'60'negOne_52 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_52 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_426 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.1<modulus
d_1'60'modulus_54 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_54
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_796 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.2*n≡n+n
d_2'42'n'8801'n'43'n_56 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_56 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.2≤modulus
d_2'8804'modulus_58 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_58 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_422 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.<⇒<ᵇtrue
d_'60''8658''60''7495'true_60 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8658''60''7495'true_60 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.InRange
d_InRange_62 :: Integer -> ()
d_InRange_62 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.Word
d_Word_64 :: ()
d_Word_64 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.fromℤ
d_fromℤ_66 :: Integer -> Integer
d_fromℤ_66
  = coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.fromℤ-0
d_fromℤ'45'0_68 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_68 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.fromℤ-in-range
d_fromℤ'45'in'45'range_70 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_70
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_174
      (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_72 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_72 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.fromℤ-neg1
d_fromℤ'45'neg1_74 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_74 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.half
d_half_76 :: Integer
d_half_76
  = coe MAlonzo.Code.Once.Word.d_half_48 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.half<modulus
d_half'60'modulus_78 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_78 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_430 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.half≡2^b
d_half'8801'2'94'b_80 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_80 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.half≤negOne
d_half'8804'negOne_82 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_82 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_450
      (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.inRange?
d_inRange'63'_84 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_84
  = coe MAlonzo.Code.Once.Word.d_inRange'63'_62 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.intMin
d_intMin_86 :: Integer
d_intMin_86
  = coe MAlonzo.Code.Once.Word.d_intMin_54 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.lit-hi
d_lit'45'hi_88 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'hi_88 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Word.du_lit'45'hi_654 v3
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.lit-lo
d_lit'45'lo_90 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'lo_90 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_lit'45'lo_666 (coe (64 :: Integer)) v2 v3
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.modulus
d_modulus_92 :: Integer
d_modulus_92
  = coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_94 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_94 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.modulus≢0
d_modulus'8802'0_96 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_96
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.mod∸half≡half
d_mod'8760'half'8801'half_98 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_98 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.mod≡half+half
d_mod'8801'half'43'half_100 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_100 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.negOne
d_negOne_102 :: Integer
d_negOne_102
  = coe MAlonzo.Code.Once.Word.d_negOne_78 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.negOne<modulus
d_negOne'60'modulus_104 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_104 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_438
      (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.negOne≢0
d_negOne'8802'0_106 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_106 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.norm
d_norm_108 :: Integer -> Integer
d_norm_108
  = coe MAlonzo.Code.Once.Word.d_norm_16 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.norm-0
d_norm'45'0_110 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_110 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.norm-id
d_norm'45'id_112 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_112 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.sdiv2ᵏ
d_sdiv2'7503'_114 :: Integer -> Integer -> Integer
d_sdiv2'7503'_114
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_138 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.shlᵂ
d_shl'7490'_116 :: Integer -> Integer -> Integer
d_shl'7490'_116
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_132 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.sucNegOne≡mod
d_sucNegOne'8801'mod_118 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_118 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.tdiv-neg1
d_tdiv'45'neg1_120 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_120 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.tmod-neg1
d_tmod'45'neg1_122 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_122 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.toWord
d_toWord_124 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_124 v0 v1
  = coe MAlonzo.Code.Once.Word.du_toWord_68 (coe (64 :: Integer)) v0
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.toWord≡fromℤ
d_toWord'8801'fromℤ_126 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'8801'fromℤ_126 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.toℤ
d_toℤ_128 :: Integer -> Integer
d_toℤ_128
  = coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.toℤ-negOne
d_toℤ'45'negOne_130 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_130 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.toℤ∘fromℤ
d_toℤ'8728'fromℤ_132 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'8728'fromℤ_132 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.unplus
d_unplus_134 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_unplus_134 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Word.du_unplus_648 v4
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.≡ᵇ-refl
d_'8801''7495''45'refl_136 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_136 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.≡ᵇ0-false
d_'8801''7495'0'45'false_138 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_138 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_140 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_140 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.⊕-neg
d_'8853''45'neg_142 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_142 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.⊕-neg-suc
d_'8853''45'neg'45'suc_144 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_144 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.⊕-normʳ
d_'8853''45'norm'691'_146 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_146 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.⊕≡+
d_'8853''8801''43'_148 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_148 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.⊖-normʳ
d_'8854''45'norm'691'_150 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_150 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.⊖≡∸
d_'8854''8801''8760'_152 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_152 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.⊗-pow2
d_'8855''45'pow2_154 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_154 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.⊝_
d_'8861'__156 :: Integer -> Integer
d_'8861'__156
  = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.⊝-fromℤ
d_'8861''45'fromℤ_158 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'fromℤ_158 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.⊝-intMin
d_'8861''45'intMin_160 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_160 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.⊝-invol-norm
d_'8861''45'invol'45'norm_162 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'invol'45'norm_162 = erased
-- Once.CCC.Target.RiscV64.AbstractToRiscV.slot-to-disp
d_slot'45'to'45'disp_164 :: Integer -> Integer
d_slot'45'to'45'disp_164 v0
  = coe
      mulInt (coe v0)
      (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_66)
-- Once.CCC.Target.RiscV64.AbstractToRiscV.compile-abstract
d_compile'45'abstract_168 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10]
d_compile'45'abstract_168 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_28
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_28
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                (coe (0 :: Integer)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_66))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe d_slot'45'to'45'disp_164 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe d_slot'45'to'45'disp_164 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                (coe (0 :: Integer)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_66))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2236 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe d_slot'45'to'45'disp_164 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2238 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe d_slot'45'to'45'disp_164 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2240 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe
                   MAlonzo.Code.Data.Integer.Base.d_'45'__260
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_68 (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2242 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_68 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2244 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2246 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe
                   MAlonzo.Code.Data.Integer.Base.d_'45'__260
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_66)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_fp_16)
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                   (coe (0 :: Integer)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_28
                      (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_fp_16)
                      (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20
                         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                         (coe
                            MAlonzo.Code.Data.Integer.Base.d_'45'__260
                            (coe
                               MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_68 (coe v1))))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2248
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_28
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_fp_16))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_fp_16)
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                   (coe (0 :: Integer)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20
                      (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                      (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_fp_16)
                      (coe
                         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_66))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2250
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s1_34)
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_66))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                   (coe
                      MAlonzo.Code.Data.Integer.Base.d_'45'__260
                      (coe
                         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_66)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_jalr_36
                      (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_ra_12)
                      (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                      (coe (0 :: Integer)))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2252 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2254 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe d_slot'45'to'45'disp_164 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2256 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe d_slot'45'to'45'disp_164 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2258 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2264 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call'45'sym_44
                (coe
                   MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_52
                   (coe MAlonzo.Code.Once.SigOp.Info.d_name_174 (coe v3))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2270 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_fits'45'int_194
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_22
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                       (coe
                          MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer)) (coe v3)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.Type.C_fits'45'float_196
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_22
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                       (coe
                          MAlonzo.Code.Once.Float.Decimal.d_round_174
                          (coe MAlonzo.Code.Once.Float.Dyadic.d_binary64_42) (coe v3)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2272 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_lla_26
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18) (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2274
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_28
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s1_34)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_22
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18) (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2278 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_unimp_48)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_28
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s2_36))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s2_36)
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s2_36)
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_68 (coe v1)))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2282 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_unimp_48)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_370
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_22
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s3_38)
                       (coe (1 :: Integer)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_372
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_22
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s3_38)
                       (coe (0 :: Integer)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s3_38)
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s3_38)
                       (coe
                          MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe (1 :: Integer))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_28
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s3_38)
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s4_40))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_22
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s4_40)
                       (coe (0 :: Integer)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s4_40)
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s4_40)
                       (coe (1 :: Integer)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_50
                       (coe MAlonzo.Code.Once.CCC.Label.C_once_24 (coe v2)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_j_38
                       (coe MAlonzo.Code.Once.CCC.Label.C_once_24 (coe v2)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2210 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_beq_30
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s3_38)
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_zero_10)
                       (coe MAlonzo.Code.Once.CCC.Label.C_once_24 (coe v2)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2212 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                       (coe (0 :: Integer)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_beq_30
                          (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                          (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_zero_10)
                          (coe MAlonzo.Code.Once.CCC.Label.C_once_24 (coe v2)))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2214 v2 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_50
                       (coe MAlonzo.Code.Once.CCC.Label.C_thunk_28 (coe v2)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20
                          (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                          (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                          (coe
                             MAlonzo.Code.Data.Integer.Base.d_'45'__260
                             (coe
                                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_68 (coe v3))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14
                             (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_ra_12)
                             (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                             (coe
                                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_68 (coe v3)))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2216 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_ra_12)
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                       (coe
                          MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_68 (coe v2)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20
                          (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                          (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                          (coe
                             MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_68
                             (coe addInt (coe (1 :: Integer)) (coe v2))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ret_40)
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2288 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe d_slot'45'to'45'disp_164 (coe v1)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_28
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s3_38))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_add_16
                      (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                      (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                      (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_add_16
                         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_add_16
                            (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                            (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                            (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_add_16
                               (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                               (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                               (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44))
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.AbstractToRiscV.compile-trace
d_compile'45'trace_242 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10]
d_compile'45'trace_242 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_compile'45'abstract_168 (coe v1))
             (coe d_compile'45'trace_242 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.AbstractToRiscV.compile-trace-cnt
d_compile'45'trace'45'cnt_248 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compile'45'trace'45'cnt_248 v0 v1 v2
  = case coe v2 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2)
      (:) v3 v4
        -> let v5
                 = coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe d_compile'45'trace'45'cnt_248 (coe v0) (coe v1) (coe v4)))
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe d_compile'45'abstract_168 (coe v3))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                           (coe d_compile'45'trace'45'cnt_248 (coe v0) (coe v1) (coe v4)))) in
           coe
             (case coe v3 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2278 v6 v7
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_compile'45'trace'45'cnt_248 (coe v0)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   d_compile'45'trace'45'cnt_248 (coe v0)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         d_compile'45'trace'45'cnt_248 (coe v0)
                                         (coe addInt (coe (2 :: Integer)) (coe v1)) (coe v6)))
                                   (coe v7)))
                             (coe v4)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                                (coe (0 :: Integer)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_beq_30
                                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_zero_10)
                                   (coe
                                      MAlonzo.Code.Once.CCC.Label.C_once_24
                                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v1))))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_compile'45'trace'45'cnt_248 (coe v0)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               d_compile'45'trace'45'cnt_248 (coe v0)
                                               (coe addInt (coe (2 :: Integer)) (coe v1)) (coe v6)))
                                         (coe v7)))
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_j_38
                                            (coe
                                               MAlonzo.Code.Once.CCC.Label.C_once_24
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                                  (coe addInt (coe (1 :: Integer)) (coe v1)))))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_50
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Label.C_once_24
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                                     (coe v1))))
                                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                      (coe
                                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               d_compile'45'trace'45'cnt_248 (coe v0)
                                               (coe addInt (coe (2 :: Integer)) (coe v1)) (coe v6)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_50
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Label.C_once_24
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                                     (coe addInt (coe (1 :: Integer)) (coe v1)))))
                                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_compile'45'trace'45'cnt_248 (coe v0)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_compile'45'trace'45'cnt_248 (coe v0)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            d_compile'45'trace'45'cnt_248 (coe v0)
                                            (coe addInt (coe (2 :: Integer)) (coe v1)) (coe v6)))
                                      (coe v7)))
                                (coe v4))))
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2282 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_compile'45'trace'45'cnt_248 (coe v0)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   d_compile'45'trace'45'cnt_248 (coe v0)
                                   (coe addInt (coe (2 :: Integer)) (coe v1)) (coe v6)))
                             (coe v4)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_50
                                (coe
                                   MAlonzo.Code.Once.CCC.Label.C_once_24
                                   (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v1))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_beq_30
                                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s3_38)
                                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_zero_10)
                                   (coe
                                      MAlonzo.Code.Once.CCC.Label.C_once_24
                                      (coe
                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                         (coe addInt (coe (1 :: Integer)) (coe v1)))))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_compile'45'trace'45'cnt_248 (coe v0)
                                         (coe addInt (coe (2 :: Integer)) (coe v1)) (coe v6)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_j_38
                                         (coe
                                            MAlonzo.Code.Once.CCC.Label.C_once_24
                                            (coe
                                               MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                               (coe v1))))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_50
                                            (coe
                                               MAlonzo.Code.Once.CCC.Label.C_once_24
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                                  (coe addInt (coe (1 :: Integer)) (coe v1)))))
                                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_compile'45'trace'45'cnt_248 (coe v0)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_compile'45'trace'45'cnt_248 (coe v0)
                                      (coe addInt (coe (2 :: Integer)) (coe v1)) (coe v6)))
                                (coe v4))))
                _ -> coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.AbstractToRiscV.compile-trace-cnt-agrees
d_compile'45'trace'45'cnt'45'agrees_322 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compile'45'trace'45'cnt'45'agrees_322 = erased
