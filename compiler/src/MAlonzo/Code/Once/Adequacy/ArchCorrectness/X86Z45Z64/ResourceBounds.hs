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
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W._%ˢ_
d__'37''738'__16 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> Integer -> Integer
d__'37''738'__16 ~v0 ~v1 = du__'37''738'__16
du__'37''738'__16 :: Integer -> Integer -> Integer
du__'37''738'__16
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__126 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W._/ˢ_
d__'47''738'__18 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> Integer -> Integer
d__'47''738'__18 ~v0 ~v1 = du__'47''738'__18
du__'47''738'__18 :: Integer -> Integer -> Integer
du__'47''738'__18
  = coe
      MAlonzo.Code.Once.Word.d__'47''738'__120 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W._<ˢ_
d__'60''738'__20 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> Integer -> Bool
d__'60''738'__20 ~v0 ~v1 = du__'60''738'__20
du__'60''738'__20 :: Integer -> Integer -> Bool
du__'60''738'__20
  = coe MAlonzo.Code.Once.Word.d__'60''738'__80 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W._≡ʷ_
d__'8801''695'__22 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> Integer -> Bool
d__'8801''695'__22 ~v0 ~v1 = du__'8801''695'__22
du__'8801''695'__22 :: Integer -> Integer -> Bool
du__'8801''695'__22
  = coe MAlonzo.Code.Once.Word.du__'8801''695'__86
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W._⊕_
d__'8853'__24 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> Integer -> Integer
d__'8853'__24 ~v0 ~v1 = du__'8853'__24
du__'8853'__24 :: Integer -> Integer -> Integer
du__'8853'__24
  = coe MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W._⊖_
d__'8854'__26 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> Integer -> Integer
d__'8854'__26 ~v0 ~v1 = du__'8854'__26
du__'8854'__26 :: Integer -> Integer -> Integer
du__'8854'__26
  = coe MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W._⊗_
d__'8855'__28 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> Integer -> Integer
d__'8855'__28 ~v0 ~v1 = du__'8855'__28
du__'8855'__28 :: Integer -> Integer -> Integer
du__'8855'__28
  = coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.%ˢ-else
d_'37''738''45'else_30 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_30 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.%ˢ-in-range
d_'37''738''45'in'45'range_32 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_32 ~v0 ~v1
  = du_'37''738''45'in'45'range_32
du_'37''738''45'in'45'range_32 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'37''738''45'in'45'range_32 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_604
      (coe (64 :: Integer)) v2 v3 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.%ˢ-mid
d_'37''738''45'mid_34 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_34 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.%ˢ-negOne
d_'37''738''45'negOne_36 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_36 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.%ˢ-zero
d_'37''738''45'zero_38 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_38 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W./ˢ-else
d_'47''738''45'else_40 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_40 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W./ˢ-in-range
d_'47''738''45'in'45'range_42 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_42 ~v0 ~v1
  = du_'47''738''45'in'45'range_42
du_'47''738''45'in'45'range_42 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'47''738''45'in'45'range_42 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_570
      (coe (64 :: Integer)) v2 v3
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W./ˢ-mid
d_'47''738''45'mid_44 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_44 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W./ˢ-negOne
d_'47''738''45'negOne_46 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_46 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W./ˢ-pow2
d_'47''738''45'pow2_48 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_48 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W./ˢ-zero
d_'47''738''45'zero_50 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_50 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.0<half
d_0'60'half_52 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_52 ~v0 ~v1 = du_0'60'half_52
du_0'60'half_52 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'half_52 = coe MAlonzo.Code.Once.Word.du_0'60'half_168
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.0<modulus
d_0'60'modulus_54 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_54 ~v0 ~v1 = du_0'60'modulus_54
du_0'60'modulus_54 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'modulus_54 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_166
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.0<negOne
d_0'60'negOne_56 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_56 ~v0 ~v1 = du_0'60'negOne_56
du_0'60'negOne_56 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'negOne_56 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_426 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.1<modulus
d_1'60'modulus_58 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_58 ~v0 ~v1 = du_1'60'modulus_58
du_1'60'modulus_58 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_1'60'modulus_58
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_796 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.2*n≡n+n
d_2'42'n'8801'n'43'n_60 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_60 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.2≤modulus
d_2'8804'modulus_62 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_62 ~v0 ~v1 = du_2'8804'modulus_62
du_2'8804'modulus_62 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_2'8804'modulus_62 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_422 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.<⇒<ᵇtrue
d_'60''8658''60''7495'true_64 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8658''60''7495'true_64 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.InRange
d_InRange_66 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> ()
d_InRange_66 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.Word
d_Word_68 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 -> ()
d_Word_68 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.fromℤ
d_fromℤ_70 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> Integer
d_fromℤ_70 ~v0 ~v1 = du_fromℤ_70
du_fromℤ_70 :: Integer -> Integer
du_fromℤ_70
  = coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.fromℤ-0
d_fromℤ'45'0_72 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_72 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.fromℤ-in-range
d_fromℤ'45'in'45'range_74 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_74 ~v0 ~v1 = du_fromℤ'45'in'45'range_74
du_fromℤ'45'in'45'range_74 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fromℤ'45'in'45'range_74
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_174
      (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_76 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_76 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.fromℤ-neg1
d_fromℤ'45'neg1_78 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_78 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.half
d_half_80 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 -> Integer
d_half_80 ~v0 ~v1 = du_half_80
du_half_80 :: Integer
du_half_80
  = coe MAlonzo.Code.Once.Word.d_half_48 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.half<modulus
d_half'60'modulus_82 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_82 ~v0 ~v1 = du_half'60'modulus_82
du_half'60'modulus_82 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_half'60'modulus_82 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_430 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.half≡2^b
d_half'8801'2'94'b_84 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_84 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.half≤negOne
d_half'8804'negOne_86 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_86 ~v0 ~v1 = du_half'8804'negOne_86
du_half'8804'negOne_86 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_half'8804'negOne_86 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_450
      (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.inRange?
d_inRange'63'_88 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_88 ~v0 ~v1 = du_inRange'63'_88
du_inRange'63'_88 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_inRange'63'_88
  = coe MAlonzo.Code.Once.Word.d_inRange'63'_62 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.intMin
d_intMin_90 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 -> Integer
d_intMin_90 ~v0 ~v1 = du_intMin_90
du_intMin_90 :: Integer
du_intMin_90
  = coe MAlonzo.Code.Once.Word.d_intMin_54 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.lit-hi
d_lit'45'hi_92 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'hi_92 ~v0 ~v1 = du_lit'45'hi_92
du_lit'45'hi_92 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lit'45'hi_92 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Word.du_lit'45'hi_654 v3
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.lit-lo
d_lit'45'lo_94 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'lo_94 ~v0 ~v1 = du_lit'45'lo_94
du_lit'45'lo_94 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lit'45'lo_94 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_lit'45'lo_666 (coe (64 :: Integer)) v2 v3
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.modulus
d_modulus_96 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 -> Integer
d_modulus_96 ~v0 ~v1 = du_modulus_96
du_modulus_96 :: Integer
du_modulus_96
  = coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_98 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_98 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.modulus≢0
d_modulus'8802'0_100 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_100 ~v0 ~v1 = du_modulus'8802'0_100
du_modulus'8802'0_100 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_modulus'8802'0_100
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.mod∸half≡half
d_mod'8760'half'8801'half_102 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_102 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.mod≡half+half
d_mod'8801'half'43'half_104 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_104 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.negOne
d_negOne_106 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 -> Integer
d_negOne_106 ~v0 ~v1 = du_negOne_106
du_negOne_106 :: Integer
du_negOne_106
  = coe MAlonzo.Code.Once.Word.d_negOne_78 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.negOne<modulus
d_negOne'60'modulus_108 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_108 ~v0 ~v1 = du_negOne'60'modulus_108
du_negOne'60'modulus_108 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_negOne'60'modulus_108 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_438
      (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.negOne≢0
d_negOne'8802'0_110 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_110 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.norm
d_norm_112 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> Integer
d_norm_112 ~v0 ~v1 = du_norm_112
du_norm_112 :: Integer -> Integer
du_norm_112
  = coe MAlonzo.Code.Once.Word.d_norm_16 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.norm-0
d_norm'45'0_114 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_114 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.norm-id
d_norm'45'id_116 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_116 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.sdiv2ᵏ
d_sdiv2'7503'_118 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> Integer -> Integer
d_sdiv2'7503'_118 ~v0 ~v1 = du_sdiv2'7503'_118
du_sdiv2'7503'_118 :: Integer -> Integer -> Integer
du_sdiv2'7503'_118
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_138 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.shlᵂ
d_shl'7490'_120 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> Integer -> Integer
d_shl'7490'_120 ~v0 ~v1 = du_shl'7490'_120
du_shl'7490'_120 :: Integer -> Integer -> Integer
du_shl'7490'_120
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_132 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.sucNegOne≡mod
d_sucNegOne'8801'mod_122 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_122 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.tdiv-neg1
d_tdiv'45'neg1_124 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_124 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.tmod-neg1
d_tmod'45'neg1_126 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_126 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.toWord
d_toWord_128 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_128 ~v0 ~v1 = du_toWord_128
du_toWord_128 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_toWord_128 v0 v1
  = coe MAlonzo.Code.Once.Word.du_toWord_68 (coe (64 :: Integer)) v0
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.toWord≡fromℤ
d_toWord'8801'fromℤ_130 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'8801'fromℤ_130 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.toℤ
d_toℤ_132 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> Integer
d_toℤ_132 ~v0 ~v1 = du_toℤ_132
du_toℤ_132 :: Integer -> Integer
du_toℤ_132
  = coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.toℤ-negOne
d_toℤ'45'negOne_134 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_134 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.toℤ∘fromℤ
d_toℤ'8728'fromℤ_136 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'8728'fromℤ_136 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.unplus
d_unplus_138 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_unplus_138 ~v0 ~v1 = du_unplus_138
du_unplus_138 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_unplus_138 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Word.du_unplus_648 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.≡ᵇ-refl
d_'8801''7495''45'refl_140 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_140 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.≡ᵇ0-false
d_'8801''7495'0'45'false_142 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_142 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_144 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_144 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.⊕-neg
d_'8853''45'neg_146 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_146 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.⊕-neg-suc
d_'8853''45'neg'45'suc_148 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_148 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.⊕-normʳ
d_'8853''45'norm'691'_150 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_150 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.⊕≡+
d_'8853''8801''43'_152 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_152 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.⊖-normʳ
d_'8854''45'norm'691'_154 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_154 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.⊖≡∸
d_'8854''8801''8760'_156 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_156 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.⊗-pow2
d_'8855''45'pow2_158 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_158 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.⊝_
d_'8861'__160 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> Integer
d_'8861'__160 ~v0 ~v1 = du_'8861'__160
du_'8861'__160 :: Integer -> Integer
du_'8861'__160
  = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.⊝-fromℤ
d_'8861''45'fromℤ_162 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'fromℤ_162 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.⊝-intMin
d_'8861''45'intMin_164 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_164 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.⊝-invol-norm
d_'8861''45'invol'45'norm_166 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'invol'45'norm_166 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.x86-64-frame-semantics
d_x86'45'64'45'frame'45'semantics_168 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6
d_x86'45'64'45'frame'45'semantics_168 ~v0 v1
  = du_x86'45'64'45'frame'45'semantics_168 v1
du_x86'45'64'45'frame'45'semantics_168 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6
du_x86'45'64'45'frame'45'semantics_168 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.HeapRoom
d_HeapRoom_170 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 -> ()
d_HeapRoom_170 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.StackRoom
d_StackRoom_182 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 -> ()
d_StackRoom_182 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.CallRoom
d_CallRoom_196 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 -> ()
d_CallRoom_196 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.RegRange
d_RegRange_208 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 -> ()
d_RegRange_208 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.ScratchDecGuarded
d_ScratchDecGuarded_220 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 -> ()
d_ScratchDecGuarded_220 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.AddrNoWrap
d_AddrNoWrap_230 a0 a1 = ()
data T_AddrNoWrap_230
  = C_constructor_296 (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_460 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
                       Integer ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_666 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_460 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_666 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_460 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_666 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.AddrNoWrap.ret-no-wrap
d_ret'45'no'45'wrap_274 ::
  T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_460 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_666 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ret'45'no'45'wrap_274 v0
  = case coe v0 of
      C_constructor_296 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.AddrNoWrap.count-no-wrap
d_count'45'no'45'wrap_284 ::
  T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_460 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_666 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_count'45'no'45'wrap_284 v0
  = case coe v0 of
      C_constructor_296 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.AddrNoWrap.lo-fits
d_lo'45'fits_294 ::
  T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_460 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_666 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'fits_294 v0
  = case coe v0 of
      C_constructor_296 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.LitFits
d_LitFits_298 a0 a1 = ()
data T_LitFits_298
  = C_constructor_348 (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_460 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
                       Integer ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_666 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_460 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
                       Integer ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_666 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.LitFits.tag-fits
d_tag'45'fits_334 ::
  T_LitFits_298 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_460 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_666 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_tag'45'fits_334 v0
  = case coe v0 of
      C_constructor_348 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.LitFits.lit-fits
d_lit'45'fits_346 ::
  T_LitFits_298 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_460 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_666 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'fits_346 v0
  = case coe v0 of
      C_constructor_348 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.float-fits
d_float'45'fits_360 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_460 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_666 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_float'45'fits_360 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9
  = du_float'45'fits_360 v6
du_float'45'fits_360 ::
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_float'45'fits_360 v0
  = coe
      MAlonzo.Code.Once.Float.Decimal.d_round'45'fits_302
      (coe MAlonzo.Code.Once.Float.Dyadic.d_binary64_42) (coe v0)
