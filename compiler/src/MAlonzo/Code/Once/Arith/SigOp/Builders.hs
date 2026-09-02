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

module MAlonzo.Code.Once.Arith.SigOp.Builders where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Float.Arith
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Arith.SigOp.Builders.W._%ˢ_
d__'37''738'__12 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d__'37''738'__12 v0
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__126
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W._/ˢ_
d__'47''738'__14 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d__'47''738'__14 v0
  = coe
      MAlonzo.Code.Once.Word.d__'47''738'__120
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W._<ˢ_
d__'60''738'__16 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Bool
d__'60''738'__16 v0
  = coe
      MAlonzo.Code.Once.Word.d__'60''738'__80
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W._≡ʷ_
d__'8801''695'__18 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Bool
d__'8801''695'__18 ~v0 = du__'8801''695'__18
du__'8801''695'__18 :: Integer -> Integer -> Bool
du__'8801''695'__18
  = coe MAlonzo.Code.Once.Word.du__'8801''695'__86
-- Once.Arith.SigOp.Builders.W._⊕_
d__'8853'__20 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d__'8853'__20 v0
  = coe
      MAlonzo.Code.Once.Word.d__'8853'__26
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W._⊖_
d__'8854'__22 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d__'8854'__22 v0
  = coe
      MAlonzo.Code.Once.Word.d__'8854'__32
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W._⊗_
d__'8855'__24 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d__'8855'__24 v0
  = coe
      MAlonzo.Code.Once.Word.d__'8855'__38
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.%ˢ-else
d_'37''738''45'else_26 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_26 = erased
-- Once.Arith.SigOp.Builders.W.%ˢ-in-range
d_'37''738''45'in'45'range_28 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_28 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_604
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0)) v3 v4
      v5
-- Once.Arith.SigOp.Builders.W.%ˢ-mid
d_'37''738''45'mid_30 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_30 = erased
-- Once.Arith.SigOp.Builders.W.%ˢ-negOne
d_'37''738''45'negOne_32 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_32 = erased
-- Once.Arith.SigOp.Builders.W.%ˢ-zero
d_'37''738''45'zero_34 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_34 = erased
-- Once.Arith.SigOp.Builders.W./ˢ-else
d_'47''738''45'else_36 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_36 = erased
-- Once.Arith.SigOp.Builders.W./ˢ-in-range
d_'47''738''45'in'45'range_38 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_38 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_570
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0)) v3 v4
-- Once.Arith.SigOp.Builders.W./ˢ-mid
d_'47''738''45'mid_40 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_40 = erased
-- Once.Arith.SigOp.Builders.W./ˢ-negOne
d_'47''738''45'negOne_42 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_42 = erased
-- Once.Arith.SigOp.Builders.W./ˢ-pow2
d_'47''738''45'pow2_44 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_44 = erased
-- Once.Arith.SigOp.Builders.W./ˢ-zero
d_'47''738''45'zero_46 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_46 = erased
-- Once.Arith.SigOp.Builders.W.0<half
d_0'60'half_48 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_48 ~v0 = du_0'60'half_48
du_0'60'half_48 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'half_48 = coe MAlonzo.Code.Once.Word.du_0'60'half_168
-- Once.Arith.SigOp.Builders.W.0<modulus
d_0'60'modulus_50 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_50 ~v0 = du_0'60'modulus_50
du_0'60'modulus_50 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'modulus_50 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_166
-- Once.Arith.SigOp.Builders.W.0<negOne
d_0'60'negOne_52 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_52 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_426
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.1<modulus
d_1'60'modulus_54 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_54 v0
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_796
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.2*n≡n+n
d_2'42'n'8801'n'43'n_56 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_56 = erased
-- Once.Arith.SigOp.Builders.W.2≤modulus
d_2'8804'modulus_58 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_58 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_422
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.<⇒<ᵇtrue
d_'60''8658''60''7495'true_60 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8658''60''7495'true_60 = erased
-- Once.Arith.SigOp.Builders.W.InRange
d_InRange_62 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> ()
d_InRange_62 = erased
-- Once.Arith.SigOp.Builders.W.Word
d_Word_64 :: MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> ()
d_Word_64 = erased
-- Once.Arith.SigOp.Builders.W.fromℤ
d_fromℤ_66 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
d_fromℤ_66 v0
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ_20
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.fromℤ-0
d_fromℤ'45'0_68 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_68 = erased
-- Once.Arith.SigOp.Builders.W.fromℤ-in-range
d_fromℤ'45'in'45'range_70 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_70 v0
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_174
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_72 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_72 = erased
-- Once.Arith.SigOp.Builders.W.fromℤ-neg1
d_fromℤ'45'neg1_74 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_74 = erased
-- Once.Arith.SigOp.Builders.W.half
d_half_76 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer
d_half_76 v0
  = coe
      MAlonzo.Code.Once.Word.d_half_48
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.half<modulus
d_half'60'modulus_78 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_78 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_430
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.half≡2^b
d_half'8801'2'94'b_80 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_80 = erased
-- Once.Arith.SigOp.Builders.W.half≤negOne
d_half'8804'negOne_82 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_82 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_450
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.inRange?
d_inRange'63'_84 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_84 v0
  = coe
      MAlonzo.Code.Once.Word.d_inRange'63'_62
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.intMin
d_intMin_86 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer
d_intMin_86 v0
  = coe
      MAlonzo.Code.Once.Word.d_intMin_54
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.lit-hi
d_lit'45'hi_88 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'hi_88 ~v0 = du_lit'45'hi_88
du_lit'45'hi_88 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lit'45'hi_88 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Word.du_lit'45'hi_654 v3
-- Once.Arith.SigOp.Builders.W.lit-lo
d_lit'45'lo_90 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'lo_90 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Word.du_lit'45'lo_666
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0)) v3 v4
-- Once.Arith.SigOp.Builders.W.modulus
d_modulus_92 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer
d_modulus_92 v0
  = coe
      MAlonzo.Code.Once.Word.d_modulus_10
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_94 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_94 = erased
-- Once.Arith.SigOp.Builders.W.modulus≢0
d_modulus'8802'0_96 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_96 v0
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.mod∸half≡half
d_mod'8760'half'8801'half_98 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_98 = erased
-- Once.Arith.SigOp.Builders.W.mod≡half+half
d_mod'8801'half'43'half_100 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_100 = erased
-- Once.Arith.SigOp.Builders.W.negOne
d_negOne_102 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer
d_negOne_102 v0
  = coe
      MAlonzo.Code.Once.Word.d_negOne_78
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.negOne<modulus
d_negOne'60'modulus_104 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_104 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_438
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.negOne≢0
d_negOne'8802'0_106 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_106 = erased
-- Once.Arith.SigOp.Builders.W.norm
d_norm_108 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
d_norm_108 v0
  = coe
      MAlonzo.Code.Once.Word.d_norm_16
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.norm-0
d_norm'45'0_110 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_110 = erased
-- Once.Arith.SigOp.Builders.W.norm-id
d_norm'45'id_112 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_112 = erased
-- Once.Arith.SigOp.Builders.W.sdiv2ᵏ
d_sdiv2'7503'_114 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d_sdiv2'7503'_114 v0
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_138
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.shlᵂ
d_shl'7490'_116 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d_shl'7490'_116 v0
  = coe
      MAlonzo.Code.Once.Word.d_shl'7490'_132
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.sucNegOne≡mod
d_sucNegOne'8801'mod_118 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_118 = erased
-- Once.Arith.SigOp.Builders.W.tdiv-neg1
d_tdiv'45'neg1_120 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_120 = erased
-- Once.Arith.SigOp.Builders.W.tmod-neg1
d_tmod'45'neg1_122 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_122 = erased
-- Once.Arith.SigOp.Builders.W.toWord
d_toWord_124 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_124 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_toWord_68
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0)) v1
-- Once.Arith.SigOp.Builders.W.toWord≡fromℤ
d_toWord'8801'fromℤ_126 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'8801'fromℤ_126 = erased
-- Once.Arith.SigOp.Builders.W.toℤ
d_toℤ_128 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
d_toℤ_128 v0
  = coe
      MAlonzo.Code.Once.Word.d_toℤ_50
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.toℤ-negOne
d_toℤ'45'negOne_130 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_130 = erased
-- Once.Arith.SigOp.Builders.W.toℤ∘fromℤ
d_toℤ'8728'fromℤ_132 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'8728'fromℤ_132 = erased
-- Once.Arith.SigOp.Builders.W.unplus
d_unplus_134 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_unplus_134 ~v0 = du_unplus_134
du_unplus_134 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_unplus_134 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Word.du_unplus_648 v4
-- Once.Arith.SigOp.Builders.W.≡ᵇ-refl
d_'8801''7495''45'refl_136 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_136 = erased
-- Once.Arith.SigOp.Builders.W.≡ᵇ0-false
d_'8801''7495'0'45'false_138 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_138 = erased
-- Once.Arith.SigOp.Builders.W.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_140 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_140 = erased
-- Once.Arith.SigOp.Builders.W.⊕-neg
d_'8853''45'neg_142 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_142 = erased
-- Once.Arith.SigOp.Builders.W.⊕-neg-suc
d_'8853''45'neg'45'suc_144 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_144 = erased
-- Once.Arith.SigOp.Builders.W.⊕-normʳ
d_'8853''45'norm'691'_146 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_146 = erased
-- Once.Arith.SigOp.Builders.W.⊕≡+
d_'8853''8801''43'_148 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_148 = erased
-- Once.Arith.SigOp.Builders.W.⊖-normʳ
d_'8854''45'norm'691'_150 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_150 = erased
-- Once.Arith.SigOp.Builders.W.⊖≡∸
d_'8854''8801''8760'_152 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_152 = erased
-- Once.Arith.SigOp.Builders.W.⊗-pow2
d_'8855''45'pow2_154 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_154 = erased
-- Once.Arith.SigOp.Builders.W.⊝_
d_'8861'__156 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
d_'8861'__156 v0
  = coe
      MAlonzo.Code.Once.Word.d_'8861'__44
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.⊝-fromℤ
d_'8861''45'fromℤ_158 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'fromℤ_158 = erased
-- Once.Arith.SigOp.Builders.W.⊝-intMin
d_'8861''45'intMin_160 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_160 = erased
-- Once.Arith.SigOp.Builders.W.⊝-invol-norm
d_'8861''45'invol'45'norm_162 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'invol'45'norm_162 = erased
-- Once.Arith.SigOp.Builders.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_166 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_166
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'base'45'to'45'full_636
-- Once.Arith.SigOp.Builders.M.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_168 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_168 = erased
-- Once.Arith.SigOp.Builders.M.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_170 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_170 = erased
-- Once.Arith.SigOp.Builders.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_172 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_172
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'full'45'to'45'base_600
-- Once.Arith.SigOp.Builders.M.coerce-functor
d_coerce'45'functor_174 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor_174 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_96 v0 v2
-- Once.Arith.SigOp.Builders.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_176 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_176 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_138
      v0 v2
-- Once.Arith.SigOp.Builders.M.coerce-round-trip
d_coerce'45'round'45'trip_178 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_178 = erased
-- Once.Arith.SigOp.Builders.M.coerce-struct
d_coerce'45'struct_180 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'struct_180
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct_268
-- Once.Arith.SigOp.Builders.M.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_182 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_182 = erased
-- Once.Arith.SigOp.Builders.M.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_184 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_184
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct'8315''185'_274
-- Once.Arith.SigOp.Builders.M.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_186 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_186 = erased
-- Once.Arith.SigOp.Builders.M.coerce-μ-in
d_coerce'45'μ'45'in_188 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_188 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'in_748 v0 v2
-- Once.Arith.SigOp.Builders.M.coerce-μ-out
d_coerce'45'μ'45'out_190 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_190 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_790 v0 v1
      v3
-- Once.Arith.SigOp.Builders.M.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_192 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_192 = erased
-- Once.Arith.SigOp.Builders.M.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_194 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_194 = erased
-- Once.Arith.SigOp.Builders.M.coerce-ν-in
d_coerce'45'ν'45'in_196 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_196
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_982
-- Once.Arith.SigOp.Builders.M.coerce-ν-out
d_coerce'45'ν'45'out_198 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_198
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'out_988
-- Once.Arith.SigOp.Builders.M.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_200 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_200 = erased
-- Once.Arith.SigOp.Builders.M.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_202 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_202 = erased
-- Once.Arith.SigOp.Builders.M.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_204 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_204 = erased
-- Once.Arith.SigOp.Builders.M.fmap-struct-coherence
d_fmap'45'struct'45'coherence_206 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_206 = erased
-- Once.Arith.SigOp.Builders.M.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_208 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_208 = erased
-- Once.Arith.SigOp.Builders.M.sem-CoIn
d_sem'45'CoIn_210 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'CoIn_210
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoIn_1002
-- Once.Arith.SigOp.Builders.M.sem-CoOut
d_sem'45'CoOut_212 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 -> AgdaAny
d_sem'45'CoOut_212
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoOut_992
-- Once.Arith.SigOp.Builders.M.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_214 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_214 = erased
-- Once.Arith.SigOp.Builders.M.sem-In
d_sem'45'In_216 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_μS_182
d_sem'45'In_216
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'In_922
-- Once.Arith.SigOp.Builders.M.sem-In-Out
d_sem'45'In'45'Out_218 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_218 = erased
-- Once.Arith.SigOp.Builders.M.sem-Out
d_sem'45'Out_220 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'Out_220
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'Out_930
-- Once.Arith.SigOp.Builders.M.sem-Out-In
d_sem'45'Out'45'In_222 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_222 = erased
-- Once.Arith.SigOp.Builders.M.sem-ana
d_sem'45'ana_224 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'ana_224 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'ana_1026 v0 v2 v3
-- Once.Arith.SigOp.Builders.M.sem-case
d_sem'45'case_226 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_226 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'case_332 v3 v4 v5
-- Once.Arith.SigOp.Builders.M.sem-case-inl
d_sem'45'case'45'inl_228 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_228 = erased
-- Once.Arith.SigOp.Builders.M.sem-case-inr
d_sem'45'case'45'inr_230 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_230 = erased
-- Once.Arith.SigOp.Builders.M.sem-cata
d_sem'45'cata_232 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'cata_232 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_942 v0 v1 v3
-- Once.Arith.SigOp.Builders.M.sem-cata-compute
d_sem'45'cata'45'compute_234 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_234 = erased
-- Once.Arith.SigOp.Builders.M.sem-fmap
d_sem'45'fmap_236 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_236 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_420 v0 v3 v4
-- Once.Arith.SigOp.Builders.M.sem-fmap-Type
d_sem'45'fmap'45'Type_238 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_238 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap'45'Type_464 v0 v3
      v4
-- Once.Arith.SigOp.Builders.M.sem-fst
d_sem'45'fst_240 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_240 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fst_296 v2
-- Once.Arith.SigOp.Builders.M.sem-fst-pair
d_sem'45'fst'45'pair_242 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_242 = erased
-- Once.Arith.SigOp.Builders.M.sem-functor-coherence
d_sem'45'functor'45'coherence_244 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_244 = erased
-- Once.Arith.SigOp.Builders.M.sem-fuseNat
d_sem'45'fuseNat_246 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'fuseNat_246 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat_1156 v0 v1 v2
      v3 v5 v6
-- Once.Arith.SigOp.Builders.M.sem-fuseNat-cong
d_sem'45'fuseNat'45'cong_248 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
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
d_sem'45'fuseNat'45'cong_248 = erased
-- Once.Arith.SigOp.Builders.M.sem-fuseNat-events
d_sem'45'fuseNat'45'events_250 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'fuseNat'45'events_250 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat'45'events_1252
      v1 v2 v3 v4 v5 v6 v8 v9
-- Once.Arith.SigOp.Builders.M.sem-inl
d_sem'45'inl_252 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_252 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inl_318
-- Once.Arith.SigOp.Builders.M.sem-inr
d_sem'45'inr_254 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_254 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inr_324
-- Once.Arith.SigOp.Builders.M.sem-pair
d_sem'45'pair_256 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_256 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'pair_308 v2 v3
-- Once.Arith.SigOp.Builders.M.sem-para
d_sem'45'para_258 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'para_258 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'para_958 v0 v1 v3 v4
-- Once.Arith.SigOp.Builders.M.sem-snd
d_sem'45'snd_260 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_260 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'snd_302 v2
-- Once.Arith.SigOp.Builders.M.sem-snd-pair
d_sem'45'snd'45'pair_262 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_262 = erased
-- Once.Arith.SigOp.Builders.M.sfmapSemAna
d_sfmapSemAna_264 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmapSemAna_264 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sfmapSemAna_1034 v0 v1 v3 v4
-- Once.Arith.SigOp.Builders.M.sfmapSemAna-is-sfmap
d_sfmapSemAna'45'is'45'sfmap_266 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapSemAna'45'is'45'sfmap_266 = erased
-- Once.Arith.SigOp.Builders.M.⟦_⟧
d_'10214'_'10215'_268 :: MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_'10214'_'10215'_268 = erased
-- Once.Arith.SigOp.Builders.M.⟦_⟧F
d_'10214'_'10215'F_270 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> ()
d_'10214'_'10215'F_270 = erased
-- Once.Arith.SigOp.Builders.M.⟦μ⟧
d_'10214'μ'10215'_272 :: MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_'10214'μ'10215'_272 = erased
-- Once.Arith.SigOp.Builders.M.⟦ν⟧
d_'10214'ν'10215'_274 :: MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_'10214'ν'10215'_274 = erased
-- Once.Arith.SigOp.Builders.add-semM
d_add'45'semM_276 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_add'45'semM_276 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Once.Word.d__'8853'__26
             (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
             (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.sub-semM
d_sub'45'semM_284 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_sub'45'semM_284 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Once.Word.d__'8854'__32
             (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
             (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.mul-semM
d_mul'45'semM_292 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_mul'45'semM_292 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Once.Word.d__'8855'__38
             (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
             (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.neg-semM
d_neg'45'semM_300 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
d_neg'45'semM_300 v0 v1
  = coe
      MAlonzo.Code.Once.Word.d_'8861'__44
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
      (coe v1)
-- Once.Arith.SigOp.Builders.fadd-semM
d_fadd'45'semM_306 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_fadd'45'semM_306 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Once.Float.Arith.d_fadd_314
             (coe MAlonzo.Code.Once.Target.Arch.d_float'45'format_24 (coe v0))
             (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.fsub-semM
d_fsub'45'semM_314 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_fsub'45'semM_314 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Once.Float.Arith.d_fsub_316
             (coe MAlonzo.Code.Once.Target.Arch.d_float'45'format_24 (coe v0))
             (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.fmul-semM
d_fmul'45'semM_322 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_fmul'45'semM_322 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Once.Float.Arith.d_fmul_318
             (coe MAlonzo.Code.Once.Target.Arch.d_float'45'format_24 (coe v0))
             (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.fdiv-semM
d_fdiv'45'semM_330 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_fdiv'45'semM_330 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Once.Float.Arith.d_fdiv_320
             (coe MAlonzo.Code.Once.Target.Arch.d_float'45'format_24 (coe v0))
             (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.i2f-semM
d_i2f'45'semM_338 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
d_i2f'45'semM_338 v0 v1
  = coe
      MAlonzo.Code.Once.Float.Arith.d_i2f_362
      (coe MAlonzo.Code.Once.Target.Arch.d_float'45'format_24 (coe v0))
      (coe
         MAlonzo.Code.Once.Word.d_toℤ_50
         (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
         (coe v1))
-- Once.Arith.SigOp.Builders.div-semM
d_div'45'semM_344
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.div-semM"
-- Once.Arith.SigOp.Builders.mod-semM
d_mod'45'semM_346
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.mod-semM"
-- Once.Arith.SigOp.Builders.lt-semM
d_lt'45'semM_348
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.lt-semM"
-- Once.Arith.SigOp.Builders.le-semM
d_le'45'semM_350
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.le-semM"
-- Once.Arith.SigOp.Builders.gt-semM
d_gt'45'semM_352
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.gt-semM"
-- Once.Arith.SigOp.Builders.ge-semM
d_ge'45'semM_354
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.ge-semM"
-- Once.Arith.SigOp.Builders.eq-semM
d_eq'45'semM_356
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.eq-semM"
-- Once.Arith.SigOp.Builders.ne-semM
d_ne'45'semM_358
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.ne-semM"
-- Once.Arith.SigOp.Builders.str-lit-semM
d_str'45'lit'45'semM_360 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_str'45'lit'45'semM_360 v0 ~v1 ~v2 = du_str'45'lit'45'semM_360 v0
du_str'45'lit'45'semM_360 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_str'45'lit'45'semM_360 v0 = coe v0
-- Once.Arith.SigOp.Builders.base-I×I
d_base'45'I'215'I_364 ::
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200
d_base'45'I'215'I_364
  = coe
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_218
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206)
-- Once.Arith.SigOp.Builders.con-Int
d_con'45'Int_366 ::
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226
d_con'45'Int_366
  = coe
      MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206)
-- Once.Arith.SigOp.Builders.con-U+U
d_con'45'U'43'U_368 ::
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226
d_con'45'U'43'U_368
  = coe
      MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230
      (coe
         MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_224
         (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)
         (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202))
-- Once.Arith.SigOp.Builders.add-info
d_add'45'info_370 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_add'45'info_370
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_238
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.add.int" :: Data.Text.Text)))
      (coe d_add'45'semM_276)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_364) (coe d_con'45'Int_366)
-- Once.Arith.SigOp.Builders.sub-info
d_sub'45'info_372 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_sub'45'info_372
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_238
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.sub.int" :: Data.Text.Text)))
      (coe d_sub'45'semM_284)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_364) (coe d_con'45'Int_366)
-- Once.Arith.SigOp.Builders.mul-info
d_mul'45'info_374 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_mul'45'info_374
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_238
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.mul.int" :: Data.Text.Text)))
      (coe d_mul'45'semM_292)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_364) (coe d_con'45'Int_366)
-- Once.Arith.SigOp.Builders.div-info
d_div'45'info_376 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_div'45'info_376
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_238
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.div.int" :: Data.Text.Text)))
      (coe d_div'45'semM_344)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_364) (coe d_con'45'Int_366)
-- Once.Arith.SigOp.Builders.mod-info
d_mod'45'info_378 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_mod'45'info_378
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_238
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.mod.int" :: Data.Text.Text)))
      (coe d_mod'45'semM_346)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_364) (coe d_con'45'Int_366)
-- Once.Arith.SigOp.Builders.neg-info
d_neg'45'info_380 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_neg'45'info_380
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_238
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.neg.int" :: Data.Text.Text)))
      (coe d_neg'45'semM_300)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206)
      (coe d_con'45'Int_366)
-- Once.Arith.SigOp.Builders.base-F×F
d_base'45'F'215'F_382 ::
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200
d_base'45'F'215'F_382
  = coe
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_218
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_208)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_208)
-- Once.Arith.SigOp.Builders.con-Float
d_con'45'Float_384 ::
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226
d_con'45'Float_384
  = coe
      MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_208)
-- Once.Arith.SigOp.Builders.fadd-info
d_fadd'45'info_386 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_fadd'45'info_386
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_238
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.add.float" :: Data.Text.Text)))
      (coe d_fadd'45'semM_306)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'F'215'F_382) (coe d_con'45'Float_384)
-- Once.Arith.SigOp.Builders.fsub-info
d_fsub'45'info_388 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_fsub'45'info_388
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_238
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.sub.float" :: Data.Text.Text)))
      (coe d_fsub'45'semM_314)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'F'215'F_382) (coe d_con'45'Float_384)
-- Once.Arith.SigOp.Builders.fmul-info
d_fmul'45'info_390 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_fmul'45'info_390
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_238
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.mul.float" :: Data.Text.Text)))
      (coe d_fmul'45'semM_322)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'F'215'F_382) (coe d_con'45'Float_384)
-- Once.Arith.SigOp.Builders.fdiv-info
d_fdiv'45'info_392 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_fdiv'45'info_392
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_238
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.div.float" :: Data.Text.Text)))
      (coe d_fdiv'45'semM_330)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'F'215'F_382) (coe d_con'45'Float_384)
-- Once.Arith.SigOp.Builders.i2f-info
d_i2f'45'info_394 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_i2f'45'info_394
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_238
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.i2f" :: Data.Text.Text)))
      (coe d_i2f'45'semM_338)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206)
      (coe d_con'45'Float_384)
-- Once.Arith.SigOp.Builders.lt-info
d_lt'45'info_396 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_lt'45'info_396
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_238
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.lt.int" :: Data.Text.Text)))
      (coe d_lt'45'semM_348)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_364) (coe d_con'45'U'43'U_368)
-- Once.Arith.SigOp.Builders.le-info
d_le'45'info_398 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_le'45'info_398
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_238
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.le.int" :: Data.Text.Text)))
      (coe d_le'45'semM_350)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_364) (coe d_con'45'U'43'U_368)
-- Once.Arith.SigOp.Builders.gt-info
d_gt'45'info_400 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_gt'45'info_400
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_238
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.gt.int" :: Data.Text.Text)))
      (coe d_gt'45'semM_352)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_364) (coe d_con'45'U'43'U_368)
-- Once.Arith.SigOp.Builders.ge-info
d_ge'45'info_402 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_ge'45'info_402
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_238
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.ge.int" :: Data.Text.Text)))
      (coe d_ge'45'semM_354)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_364) (coe d_con'45'U'43'U_368)
-- Once.Arith.SigOp.Builders.eq-info
d_eq'45'info_404 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_eq'45'info_404
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_238
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.eq.int" :: Data.Text.Text)))
      (coe d_eq'45'semM_356)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_364) (coe d_con'45'U'43'U_368)
-- Once.Arith.SigOp.Builders.ne-info
d_ne'45'info_406 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_ne'45'info_406
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_238
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.ne.int" :: Data.Text.Text)))
      (coe d_ne'45'semM_358)
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe d_base'45'I'215'I_364) (coe d_con'45'U'43'U_368)
-- Once.Arith.SigOp.Builders.str-lit-info
d_str'45'lit'45'info_408 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_str'45'lit'45'info_408 v0
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_238
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            ("lit.str." :: Data.Text.Text) v0))
      (coe (\ v1 v2 -> v0)) (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)
      (coe
         MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230
         (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Str_210))
-- Once.Arith.SigOp.Builders.generic-semM
d_generic'45'semM_416
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.generic-semM"
-- Once.Arith.SigOp.Builders.value-info
d_value'45'info_422 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_value'45'info_422 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_238 (coe v2)
      (coe
         d_generic'45'semM_416 v0 v1
         (MAlonzo.Code.Once.CanonicalName.d_showCanonical_134 (coe v2)))
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124) (coe v3) (coe v4)
-- Once.Arith.SigOp.Builders.internal-info
d_internal'45'info_432 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_internal'45'info_432 v0 v1
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_182 (coe v1)
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_pureV_140
         (coe
            d_generic'45'semM_416 (coe MAlonzo.Code.Once.Type.C_Unit_118) v0
            (MAlonzo.Code.Once.CanonicalName.d_showCanonical_134 (coe v1))))
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)
      (coe MAlonzo.Code.Once.SigOp.Info.C_internal'45'ref_154)
-- Once.Arith.SigOp.Builders.generic-info
d_generic'45'info_440 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_generic'45'info_440 v0 v1
  = coe d_value'45'info_422 (coe v0) (coe v1)
-- Once.Arith.SigOp.Builders.arrow-info-eff
d_arrow'45'info'45'eff_446 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_arrow'45'info'45'eff_446 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
        -> if coe v6
             then coe
                    seq (coe v7)
                    (coe
                       MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_182 (coe v2)
                       (coe MAlonzo.Code.Once.SigOp.Info.C_emitsV_142) (coe v4)
                       (coe MAlonzo.Code.Once.SigOp.Info.C_ffi'45'concrete_152 (coe v5)))
             else coe
                    seq (coe v7)
                    (coe
                       d_value'45'info_422 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.arrow-info
d_arrow'45'info_464 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_arrow'45'info_464 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      MAlonzo.Code.Once.Type.C_mk'45'kind_50 v6 v7
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C_pure_34
               -> coe
                    d_value'45'info_422 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
             MAlonzo.Code.Once.Type.C_eff_36
               -> coe
                    d_arrow'45'info'45'eff_446 (coe v0) (coe v1) (coe v3)
                    (coe MAlonzo.Code.Once.Type.d_isUnit'63'_160 (coe v1)) (coe v4)
                    (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
