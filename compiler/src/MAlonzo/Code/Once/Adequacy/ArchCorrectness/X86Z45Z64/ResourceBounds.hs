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
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Word

-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W._%ˢ_
d__'37''738'__14 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> Integer -> Integer
d__'37''738'__14 ~v0 = du__'37''738'__14
du__'37''738'__14 :: Integer -> Integer -> Integer
du__'37''738'__14
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__104 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W._/ˢ_
d__'47''738'__16 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> Integer -> Integer
d__'47''738'__16 ~v0 = du__'47''738'__16
du__'47''738'__16 :: Integer -> Integer -> Integer
du__'47''738'__16
  = coe MAlonzo.Code.Once.Word.d__'47''738'__98 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W._<ˢ_
d__'60''738'__18 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> Integer -> Bool
d__'60''738'__18 ~v0 = du__'60''738'__18
du__'60''738'__18 :: Integer -> Integer -> Bool
du__'60''738'__18
  = coe MAlonzo.Code.Once.Word.d__'60''738'__58 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W._≡ʷ_
d__'8801''695'__20 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> Integer -> Bool
d__'8801''695'__20 ~v0 = du__'8801''695'__20
du__'8801''695'__20 :: Integer -> Integer -> Bool
du__'8801''695'__20
  = coe MAlonzo.Code.Once.Word.du__'8801''695'__64
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W._⊕_
d__'8853'__22 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> Integer -> Integer
d__'8853'__22 ~v0 = du__'8853'__22
du__'8853'__22 :: Integer -> Integer -> Integer
du__'8853'__22
  = coe MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W._⊖_
d__'8854'__24 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> Integer -> Integer
d__'8854'__24 ~v0 = du__'8854'__24
du__'8854'__24 :: Integer -> Integer -> Integer
du__'8854'__24
  = coe MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W._⊗_
d__'8855'__26 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> Integer -> Integer
d__'8855'__26 ~v0 = du__'8855'__26
du__'8855'__26 :: Integer -> Integer -> Integer
du__'8855'__26
  = coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.%ˢ-else
d_'37''738''45'else_28 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_28 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.%ˢ-in-range
d_'37''738''45'in'45'range_30 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_30 ~v0 = du_'37''738''45'in'45'range_30
du_'37''738''45'in'45'range_30 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'37''738''45'in'45'range_30 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_526
      (coe (64 :: Integer)) v2 v3 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.%ˢ-mid
d_'37''738''45'mid_32 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_32 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.%ˢ-negOne
d_'37''738''45'negOne_34 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_34 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.%ˢ-zero
d_'37''738''45'zero_36 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_36 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W./ˢ-else
d_'47''738''45'else_38 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_38 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W./ˢ-in-range
d_'47''738''45'in'45'range_40 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_40 ~v0 = du_'47''738''45'in'45'range_40
du_'47''738''45'in'45'range_40 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'47''738''45'in'45'range_40 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_492
      (coe (64 :: Integer)) v2 v3
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W./ˢ-mid
d_'47''738''45'mid_42 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_42 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W./ˢ-negOne
d_'47''738''45'negOne_44 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_44 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W./ˢ-pow2
d_'47''738''45'pow2_46 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_46 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W./ˢ-zero
d_'47''738''45'zero_48 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_48 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.0<half
d_0'60'half_50 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_50 ~v0 = du_0'60'half_50
du_0'60'half_50 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'half_50 = coe MAlonzo.Code.Once.Word.du_0'60'half_146
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.0<modulus
d_0'60'modulus_52 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_52 ~v0 = du_0'60'modulus_52
du_0'60'modulus_52 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'modulus_52 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_144
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.0<negOne
d_0'60'negOne_54 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_54 ~v0 = du_0'60'negOne_54
du_0'60'negOne_54 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'negOne_54 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_348 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.1<modulus
d_1'60'modulus_56 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_56 ~v0 = du_1'60'modulus_56
du_1'60'modulus_56 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_1'60'modulus_56
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_628 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.2*n≡n+n
d_2'42'n'8801'n'43'n_58 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_58 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.2≤modulus
d_2'8804'modulus_60 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_60 ~v0 = du_2'8804'modulus_60
du_2'8804'modulus_60 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_2'8804'modulus_60 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_344 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.Word
d_Word_62 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> ()
d_Word_62 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.fromℤ
d_fromℤ_64 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> Integer
d_fromℤ_64 ~v0 = du_fromℤ_64
du_fromℤ_64 :: Integer -> Integer
du_fromℤ_64
  = coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.fromℤ-0
d_fromℤ'45'0_66 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_66 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.fromℤ-in-range
d_fromℤ'45'in'45'range_68 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_68 ~v0 = du_fromℤ'45'in'45'range_68
du_fromℤ'45'in'45'range_68 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fromℤ'45'in'45'range_68
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_152
      (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_70 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_70 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.fromℤ-neg1
d_fromℤ'45'neg1_72 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_72 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.half
d_half_74 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> Integer
d_half_74 ~v0 = du_half_74
du_half_74 :: Integer
du_half_74
  = coe MAlonzo.Code.Once.Word.d_half_48 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.half<modulus
d_half'60'modulus_76 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_76 ~v0 = du_half'60'modulus_76
du_half'60'modulus_76 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_half'60'modulus_76 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_352 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.half≡2^b
d_half'8801'2'94'b_78 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_78 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.half≤negOne
d_half'8804'negOne_80 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_80 ~v0 = du_half'8804'negOne_80
du_half'8804'negOne_80 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_half'8804'negOne_80 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_372
      (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.intMin
d_intMin_82 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> Integer
d_intMin_82 ~v0 = du_intMin_82
du_intMin_82 :: Integer
du_intMin_82
  = coe MAlonzo.Code.Once.Word.d_intMin_54 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.modulus
d_modulus_84 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> Integer
d_modulus_84 ~v0 = du_modulus_84
du_modulus_84 :: Integer
du_modulus_84
  = coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_86 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_86 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.modulus≢0
d_modulus'8802'0_88 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_88 ~v0 = du_modulus'8802'0_88
du_modulus'8802'0_88 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_modulus'8802'0_88
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.mod∸half≡half
d_mod'8760'half'8801'half_90 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_90 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.mod≡half+half
d_mod'8801'half'43'half_92 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_92 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.negOne
d_negOne_94 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> Integer
d_negOne_94 ~v0 = du_negOne_94
du_negOne_94 :: Integer
du_negOne_94
  = coe MAlonzo.Code.Once.Word.d_negOne_56 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.negOne<modulus
d_negOne'60'modulus_96 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_96 ~v0 = du_negOne'60'modulus_96
du_negOne'60'modulus_96 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_negOne'60'modulus_96 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_360
      (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.negOne≢0
d_negOne'8802'0_98 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_98 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.norm
d_norm_100 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> Integer
d_norm_100 ~v0 = du_norm_100
du_norm_100 :: Integer -> Integer
du_norm_100
  = coe MAlonzo.Code.Once.Word.d_norm_16 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.norm-0
d_norm'45'0_102 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_102 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.norm-id
d_norm'45'id_104 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_104 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.sdiv2ᵏ
d_sdiv2'7503'_106 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> Integer -> Integer
d_sdiv2'7503'_106 ~v0 = du_sdiv2'7503'_106
du_sdiv2'7503'_106 :: Integer -> Integer -> Integer
du_sdiv2'7503'_106
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_116 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.shlᵂ
d_shl'7490'_108 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> Integer -> Integer
d_shl'7490'_108 ~v0 = du_shl'7490'_108
du_shl'7490'_108 :: Integer -> Integer -> Integer
du_shl'7490'_108
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_110 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.sucNegOne≡mod
d_sucNegOne'8801'mod_110 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_110 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.tdiv-neg1
d_tdiv'45'neg1_112 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_112 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.tmod-neg1
d_tmod'45'neg1_114 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_114 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.toℤ
d_toℤ_116 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> Integer
d_toℤ_116 ~v0 = du_toℤ_116
du_toℤ_116 :: Integer -> Integer
du_toℤ_116
  = coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.toℤ-negOne
d_toℤ'45'negOne_118 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_118 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.≡ᵇ-refl
d_'8801''7495''45'refl_120 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_120 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.≡ᵇ0-false
d_'8801''7495'0'45'false_122 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_122 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_124 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_124 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.⊕-neg
d_'8853''45'neg_126 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_126 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.⊕-neg-suc
d_'8853''45'neg'45'suc_128 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_128 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.⊕-normʳ
d_'8853''45'norm'691'_130 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_130 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.⊕≡+
d_'8853''8801''43'_132 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_132 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.⊖-normʳ
d_'8854''45'norm'691'_134 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_134 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.⊖≡∸
d_'8854''8801''8760'_136 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_136 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.⊗-pow2
d_'8855''45'pow2_138 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_138 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.⊝_
d_'8861'__140 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> Integer
d_'8861'__140 ~v0 = du_'8861'__140
du_'8861'__140 :: Integer -> Integer
du_'8861'__140
  = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.W.⊝-intMin
d_'8861''45'intMin_142 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_142 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.HeapRoom
d_HeapRoom_144 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> ()
d_HeapRoom_144 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.StackRoom
d_StackRoom_156 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> ()
d_StackRoom_156 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.CallRoom
d_CallRoom_170 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> ()
d_CallRoom_170 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.RegRange
d_RegRange_180 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> ()
d_RegRange_180 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.ScratchDecGuarded
d_ScratchDecGuarded_192 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> ()
d_ScratchDecGuarded_192 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.AddrNoWrap
d_AddrNoWrap_202 a0 = ()
data T_AddrNoWrap_202
  = C_constructor_268 (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_338 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_348 ->
                       Integer ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_264 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_644 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_338 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_348 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_264 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_644 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_338 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_348 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_264 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_644 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.AddrNoWrap.ret-no-wrap
d_ret'45'no'45'wrap_246 ::
  T_AddrNoWrap_202 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_338 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_348 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_264 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_644 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ret'45'no'45'wrap_246 v0
  = case coe v0 of
      C_constructor_268 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.AddrNoWrap.count-no-wrap
d_count'45'no'45'wrap_256 ::
  T_AddrNoWrap_202 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_338 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_348 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_264 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_644 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_count'45'no'45'wrap_256 v0
  = case coe v0 of
      C_constructor_268 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.AddrNoWrap.lo-fits
d_lo'45'fits_266 ::
  T_AddrNoWrap_202 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_338 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_348 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_264 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_644 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'fits_266 v0
  = case coe v0 of
      C_constructor_268 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.LitFits
d_LitFits_270 a0 = ()
data T_LitFits_270
  = C_constructor_344 (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_338 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_348 ->
                       Integer ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_264 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_644 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_338 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_348 ->
                       Integer ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_264 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_644 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_338 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_348 ->
                       MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_264 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_644 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.LitFits.tag-fits
d_tag'45'fits_318 ::
  T_LitFits_270 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_338 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_348 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_264 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_644 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_tag'45'fits_318 v0
  = case coe v0 of
      C_constructor_344 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.LitFits.lit-fits
d_lit'45'fits_330 ::
  T_LitFits_270 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_338 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_348 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_264 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_644 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'fits_330 v0
  = case coe v0 of
      C_constructor_344 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.LitFits.float-fits
d_float'45'fits_342 ::
  T_LitFits_270 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_338 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_348 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_264 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_644 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_float'45'fits_342 v0
  = case coe v0 of
      C_constructor_344 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
