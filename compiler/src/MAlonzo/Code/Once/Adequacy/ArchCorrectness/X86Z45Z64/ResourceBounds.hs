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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics
import qualified MAlonzo.Code.Once.Float.DecimalLaws
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Word
import qualified MAlonzo.Code.Once.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W._%ˢ_
d__'37''738'__16 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer -> Integer -> Integer
d__'37''738'__16 ~v0 ~v1 = du__'37''738'__16
du__'37''738'__16 :: Integer -> Integer -> Integer
du__'37''738'__16
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'37''738'__122 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W._/ˢ_
d__'47''738'__18 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer -> Integer -> Integer
d__'47''738'__18 ~v0 ~v1 = du__'47''738'__18
du__'47''738'__18 :: Integer -> Integer -> Integer
du__'47''738'__18
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'47''738'__116 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W._<ˢ_
d__'60''738'__20 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer -> Integer -> Bool
d__'60''738'__20 ~v0 ~v1 = du__'60''738'__20
du__'60''738'__20 :: Integer -> Integer -> Bool
du__'60''738'__20
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'60''738'__76 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W._divℕ_
d__divℕ__22 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer -> Integer -> Integer
d__divℕ__22 ~v0 ~v1 = du__divℕ__22
du__divℕ__22 :: Integer -> Integer -> Integer
du__divℕ__22 = coe MAlonzo.Code.Once.Spec.Word.du__divℕ__88
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W._modℕ_
d__modℕ__24 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer -> Integer -> Integer
d__modℕ__24 ~v0 ~v1 = du__modℕ__24
du__modℕ__24 :: Integer -> Integer -> Integer
du__modℕ__24 = coe MAlonzo.Code.Once.Spec.Word.du__modℕ__90
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W._≡ʷ_
d__'8801''695'__26 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer -> Integer -> Bool
d__'8801''695'__26 ~v0 ~v1 = du__'8801''695'__26
du__'8801''695'__26 :: Integer -> Integer -> Bool
du__'8801''695'__26
  = coe MAlonzo.Code.Once.Spec.Word.du__'8801''695'__82
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W._⊕_
d__'8853'__28 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer -> Integer -> Integer
d__'8853'__28 ~v0 ~v1 = du__'8853'__28
du__'8853'__28 :: Integer -> Integer -> Integer
du__'8853'__28
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8853'__28 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W._⊖_
d__'8854'__30 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer -> Integer -> Integer
d__'8854'__30 ~v0 ~v1 = du__'8854'__30
du__'8854'__30 :: Integer -> Integer -> Integer
du__'8854'__30
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8854'__34 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W._⊗_
d__'8855'__32 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer -> Integer -> Integer
d__'8855'__32 ~v0 ~v1 = du__'8855'__32
du__'8855'__32 :: Integer -> Integer -> Integer
du__'8855'__32
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8855'__40 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.InRange
d_InRange_34 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 -> Integer -> ()
d_InRange_34 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.Word
d_Word_36 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 -> ()
d_Word_36 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.fromℤ
d_fromℤ_38 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 -> Integer -> Integer
d_fromℤ_38 ~v0 ~v1 = du_fromℤ_38
du_fromℤ_38 :: Integer -> Integer
du_fromℤ_38
  = coe MAlonzo.Code.Once.Spec.Word.d_fromℤ_22 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.half
d_half_40 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 -> Integer
d_half_40 ~v0 ~v1 = du_half_40
du_half_40 :: Integer
du_half_40
  = coe MAlonzo.Code.Once.Spec.Word.d_half_50 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.inRange?
d_inRange'63'_42 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_42 ~v0 ~v1 = du_inRange'63'_42
du_inRange'63'_42 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_inRange'63'_42
  = coe
      MAlonzo.Code.Once.Spec.Word.d_inRange'63'_66 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.intMin
d_intMin_44 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 -> Integer
d_intMin_44 ~v0 ~v1 = du_intMin_44
du_intMin_44 :: Integer
du_intMin_44
  = coe MAlonzo.Code.Once.Spec.Word.d_intMin_56 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.modulus
d_modulus_46 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 -> Integer
d_modulus_46 ~v0 ~v1 = du_modulus_46
du_modulus_46 :: Integer
du_modulus_46
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.modulus≢0
d_modulus'8802'0_48 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_48 ~v0 ~v1 = du_modulus'8802'0_48
du_modulus'8802'0_48 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_modulus'8802'0_48
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus'8802'0_14
      (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.negOne
d_negOne_50 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 -> Integer
d_negOne_50 ~v0 ~v1 = du_negOne_50
du_negOne_50 :: Integer
du_negOne_50
  = coe MAlonzo.Code.Once.Spec.Word.d_negOne_58 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.norm
d_norm_52 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 -> Integer -> Integer
d_norm_52 ~v0 ~v1 = du_norm_52
du_norm_52 :: Integer -> Integer
du_norm_52
  = coe MAlonzo.Code.Once.Spec.Word.d_norm_18 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.tdivℤ
d_tdivℤ_54 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer -> Integer -> Integer
d_tdivℤ_54 ~v0 ~v1 = du_tdivℤ_54
du_tdivℤ_54 :: Integer -> Integer -> Integer
du_tdivℤ_54 = coe MAlonzo.Code.Once.Spec.Word.du_tdivℤ_104
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.tmodℤ
d_tmodℤ_56 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer -> Integer -> Integer
d_tmodℤ_56 ~v0 ~v1 = du_tmodℤ_56
du_tmodℤ_56 :: Integer -> Integer -> Integer
du_tmodℤ_56 = coe MAlonzo.Code.Once.Spec.Word.du_tmodℤ_106
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.toWord
d_toWord_58 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_58 ~v0 ~v1 = du_toWord_58
du_toWord_58 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_toWord_58 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Word.du_toWord_72 (coe (64 :: Integer)) v0
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.toℤ
d_toℤ_60 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 -> Integer -> Integer
d_toℤ_60 ~v0 ~v1 = du_toℤ_60
du_toℤ_60 :: Integer -> Integer
du_toℤ_60
  = coe MAlonzo.Code.Once.Spec.Word.d_toℤ_52 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.⊝_
d_'8861'__62 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 -> Integer -> Integer
d_'8861'__62 ~v0 ~v1 = du_'8861'__62
du_'8861'__62 :: Integer -> Integer
du_'8861'__62
  = coe
      MAlonzo.Code.Once.Spec.Word.d_'8861'__46 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.%ˢ-else
d_'37''738''45'else_66 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_66 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.%ˢ-in-range
d_'37''738''45'in'45'range_68 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_68 ~v0 ~v1
  = du_'37''738''45'in'45'range_68
du_'37''738''45'in'45'range_68 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'37''738''45'in'45'range_68 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_530
      (coe (64 :: Integer)) v2 v3 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.%ˢ-mid
d_'37''738''45'mid_70 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_70 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.%ˢ-negOne
d_'37''738''45'negOne_72 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_72 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.%ˢ-zero
d_'37''738''45'zero_74 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_74 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL./ˢ-else
d_'47''738''45'else_76 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_76 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL./ˢ-in-range
d_'47''738''45'in'45'range_78 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_78 ~v0 ~v1
  = du_'47''738''45'in'45'range_78
du_'47''738''45'in'45'range_78 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'47''738''45'in'45'range_78 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_496
      (coe (64 :: Integer)) v2 v3
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL./ˢ-mid
d_'47''738''45'mid_80 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_80 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL./ˢ-negOne
d_'47''738''45'negOne_82 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_82 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL./ˢ-pow2
d_'47''738''45'pow2_84 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_84 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL./ˢ-zero
d_'47''738''45'zero_86 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_86 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.0<half
d_0'60'half_88 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_88 ~v0 ~v1 = du_0'60'half_88
du_0'60'half_88 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'half_88 = coe MAlonzo.Code.Once.Word.du_0'60'half_100
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.0<modulus
d_0'60'modulus_90 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_90 ~v0 ~v1 = du_0'60'modulus_90
du_0'60'modulus_90 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'modulus_90 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_98
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.0<negOne
d_0'60'negOne_92 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_92 ~v0 ~v1 = du_0'60'negOne_92
du_0'60'negOne_92 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'negOne_92 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_352 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.1<modulus
d_1'60'modulus_94 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_94 ~v0 ~v1 = du_1'60'modulus_94
du_1'60'modulus_94 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_1'60'modulus_94
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_722 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.2*n≡n+n
d_2'42'n'8801'n'43'n_96 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_96 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.2≤modulus
d_2'8804'modulus_98 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_98 ~v0 ~v1 = du_2'8804'modulus_98
du_2'8804'modulus_98 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_2'8804'modulus_98 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_348 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.<⇒<ᵇtrue
d_'60''8658''60''7495'true_100 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8658''60''7495'true_100 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.fromℤ-0
d_fromℤ'45'0_102 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_102 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.fromℤ-in-range
d_fromℤ'45'in'45'range_104 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_104 ~v0 ~v1 = du_fromℤ'45'in'45'range_104
du_fromℤ'45'in'45'range_104 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fromℤ'45'in'45'range_104
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_106
      (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_106 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_106 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.fromℤ-neg1
d_fromℤ'45'neg1_108 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_108 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.half<modulus
d_half'60'modulus_110 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_110 ~v0 ~v1 = du_half'60'modulus_110
du_half'60'modulus_110 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_half'60'modulus_110 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_356 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.half≡2^b
d_half'8801'2'94'b_112 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_112 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.half≤negOne
d_half'8804'negOne_114 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_114 ~v0 ~v1 = du_half'8804'negOne_114
du_half'8804'negOne_114 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_half'8804'negOne_114 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_376
      (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.lit-hi
d_lit'45'hi_116 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'hi_116 ~v0 ~v1 = du_lit'45'hi_116
du_lit'45'hi_116 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lit'45'hi_116 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Word.du_lit'45'hi_580 v3
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.lit-lo
d_lit'45'lo_118 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'lo_118 ~v0 ~v1 = du_lit'45'lo_118
du_lit'45'lo_118 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lit'45'lo_118 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_lit'45'lo_592 (coe (64 :: Integer)) v2 v3
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_120 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_120 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.mod∸half≡half
d_mod'8760'half'8801'half_122 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_122 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.mod≡half+half
d_mod'8801'half'43'half_124 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_124 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.negOne<modulus
d_negOne'60'modulus_126 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_126 ~v0 ~v1 = du_negOne'60'modulus_126
du_negOne'60'modulus_126 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_negOne'60'modulus_126 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_364
      (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.negOne≢0
d_negOne'8802'0_128 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_128 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.norm-0
d_norm'45'0_130 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_130 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.norm-id
d_norm'45'id_132 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_132 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.sbb-pos
d_sbb'45'pos_134 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sbb'45'pos_134 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.sbb-zero
d_sbb'45'zero_136 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sbb'45'zero_136 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.sdiv2ᵏ
d_sdiv2'7503'_138 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer -> Integer -> Integer
d_sdiv2'7503'_138 ~v0 ~v1 = du_sdiv2'7503'_138
du_sdiv2'7503'_138 :: Integer -> Integer -> Integer
du_sdiv2'7503'_138
  = coe MAlonzo.Code.Once.Word.d_sdiv2'7503'_70 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.shlᵂ
d_shl'7490'_140 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer -> Integer -> Integer
d_shl'7490'_140 ~v0 ~v1 = du_shl'7490'_140
du_shl'7490'_140 :: Integer -> Integer -> Integer
du_shl'7490'_140
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_64 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.sucNegOne≡mod
d_sucNegOne'8801'mod_142 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_142 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.tdiv-neg1
d_tdiv'45'neg1_144 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_144 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.tmod-neg1
d_tmod'45'neg1_146 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_146 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.toWord≡fromℤ
d_toWord'8801'fromℤ_148 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'8801'fromℤ_148 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.toℤ-negOne
d_toℤ'45'negOne_150 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_150 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.toℤ∘fromℤ
d_toℤ'8728'fromℤ_152 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'8728'fromℤ_152 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.unplus
d_unplus_154 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_unplus_154 ~v0 ~v1 = du_unplus_154
du_unplus_154 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_unplus_154 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Word.du_unplus_574 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.≡ᵇ0-false
d_'8801''7495'0'45'false_156 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_156 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_158 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_158 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.⊕-neg
d_'8853''45'neg_160 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_160 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.⊕-neg-suc
d_'8853''45'neg'45'suc_162 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_162 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.⊕-normʳ
d_'8853''45'norm'691'_164 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_164 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.⊕≡+
d_'8853''8801''43'_166 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_166 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.⊖-normʳ
d_'8854''45'norm'691'_168 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_168 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.⊖-self
d_'8854''45'self_170 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'self_170 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.⊖≡∸
d_'8854''8801''8760'_172 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_172 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.⊗-pow2
d_'8855''45'pow2_174 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_174 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.⊝-fromℤ
d_'8861''45'fromℤ_176 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'fromℤ_176 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.⊝-intMin
d_'8861''45'intMin_178 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_178 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.WL.⊝-invol-norm
d_'8861''45'invol'45'norm_180 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'invol'45'norm_180 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.x86-64-frame-semantics
d_x86'45'64'45'frame'45'semantics_182 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6
d_x86'45'64'45'frame'45'semantics_182 ~v0 v1
  = du_x86'45'64'45'frame'45'semantics_182 v1
du_x86'45'64'45'frame'45'semantics_182 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6
du_x86'45'64'45'frame'45'semantics_182 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_246
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.HeapRoom
d_HeapRoom_184 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 -> ()
d_HeapRoom_184 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.StackRoom
d_StackRoom_196 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 -> ()
d_StackRoom_196 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.CallRoom
d_CallRoom_210 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 -> ()
d_CallRoom_210 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.RegRange
d_RegRange_222 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 -> ()
d_RegRange_222 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.ScratchDecGuarded
d_ScratchDecGuarded_234 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 -> ()
d_ScratchDecGuarded_234 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.AddrNoWrap
d_AddrNoWrap_244 a0 a1 = ()
data T_AddrNoWrap_244
  = C_constructor_310 (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2246] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
                       Integer ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2246] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2246] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.AddrNoWrap.ret-no-wrap
d_ret'45'no'45'wrap_288 ::
  T_AddrNoWrap_244 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2246] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ret'45'no'45'wrap_288 v0
  = case coe v0 of
      C_constructor_310 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.AddrNoWrap.count-no-wrap
d_count'45'no'45'wrap_298 ::
  T_AddrNoWrap_244 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2246] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_count'45'no'45'wrap_298 v0
  = case coe v0 of
      C_constructor_310 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.AddrNoWrap.lo-fits
d_lo'45'fits_308 ::
  T_AddrNoWrap_244 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2246] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'fits_308 v0
  = case coe v0 of
      C_constructor_310 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.LitFits
d_LitFits_312 a0 a1 = ()
data T_LitFits_312
  = C_constructor_362 (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2246] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
                       Integer ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2246] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
                       Integer ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.LitFits.tag-fits
d_tag'45'fits_348 ::
  T_LitFits_312 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2246] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_tag'45'fits_348 v0
  = case coe v0 of
      C_constructor_362 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.LitFits.lit-fits
d_lit'45'fits_360 ::
  T_LitFits_312 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2246] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'fits_360 v0
  = case coe v0 of
      C_constructor_362 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.float-fits
d_float'45'fits_374 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2246] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Once.Spec.Float.Decimal.T_Decimal_8 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_float'45'fits_374 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9
  = du_float'45'fits_374 v6
du_float'45'fits_374 ::
  MAlonzo.Code.Once.Spec.Float.Decimal.T_Decimal_8 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_float'45'fits_374 v0
  = coe
      MAlonzo.Code.Once.Float.DecimalLaws.d_round'45'fits_128
      (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_binary64_44) (coe v0)
