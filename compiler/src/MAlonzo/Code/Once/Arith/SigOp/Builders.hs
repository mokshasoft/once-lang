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
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.Arith.Prim
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Res
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
-- Once.Arith.SigOp.Builders.W.sbb-pos
d_sbb'45'pos_114 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sbb'45'pos_114 = erased
-- Once.Arith.SigOp.Builders.W.sbb-zero
d_sbb'45'zero_116 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sbb'45'zero_116 = erased
-- Once.Arith.SigOp.Builders.W.sdiv2ᵏ
d_sdiv2'7503'_118 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d_sdiv2'7503'_118 v0
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_138
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.shlᵂ
d_shl'7490'_120 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d_shl'7490'_120 v0
  = coe
      MAlonzo.Code.Once.Word.d_shl'7490'_132
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.sucNegOne≡mod
d_sucNegOne'8801'mod_122 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_122 = erased
-- Once.Arith.SigOp.Builders.W.tdiv-neg1
d_tdiv'45'neg1_124 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_124 = erased
-- Once.Arith.SigOp.Builders.W.tmod-neg1
d_tmod'45'neg1_126 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_126 = erased
-- Once.Arith.SigOp.Builders.W.toWord
d_toWord_128 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_128 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_toWord_68
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0)) v1
-- Once.Arith.SigOp.Builders.W.toWord≡fromℤ
d_toWord'8801'fromℤ_130 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'8801'fromℤ_130 = erased
-- Once.Arith.SigOp.Builders.W.toℤ
d_toℤ_132 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
d_toℤ_132 v0
  = coe
      MAlonzo.Code.Once.Word.d_toℤ_50
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.toℤ-negOne
d_toℤ'45'negOne_134 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_134 = erased
-- Once.Arith.SigOp.Builders.W.toℤ∘fromℤ
d_toℤ'8728'fromℤ_136 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'8728'fromℤ_136 = erased
-- Once.Arith.SigOp.Builders.W.unplus
d_unplus_138 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_unplus_138 ~v0 = du_unplus_138
du_unplus_138 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_unplus_138 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Word.du_unplus_648 v4
-- Once.Arith.SigOp.Builders.W.≡ᵇ-refl
d_'8801''7495''45'refl_140 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_140 = erased
-- Once.Arith.SigOp.Builders.W.≡ᵇ0-false
d_'8801''7495'0'45'false_142 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_142 = erased
-- Once.Arith.SigOp.Builders.W.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_144 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_144 = erased
-- Once.Arith.SigOp.Builders.W.⊕-neg
d_'8853''45'neg_146 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_146 = erased
-- Once.Arith.SigOp.Builders.W.⊕-neg-suc
d_'8853''45'neg'45'suc_148 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_148 = erased
-- Once.Arith.SigOp.Builders.W.⊕-normʳ
d_'8853''45'norm'691'_150 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_150 = erased
-- Once.Arith.SigOp.Builders.W.⊕≡+
d_'8853''8801''43'_152 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_152 = erased
-- Once.Arith.SigOp.Builders.W.⊖-normʳ
d_'8854''45'norm'691'_154 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_154 = erased
-- Once.Arith.SigOp.Builders.W.⊖-self
d_'8854''45'self_156 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'self_156 = erased
-- Once.Arith.SigOp.Builders.W.⊖≡∸
d_'8854''8801''8760'_158 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_158 = erased
-- Once.Arith.SigOp.Builders.W.⊗-pow2
d_'8855''45'pow2_160 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_160 = erased
-- Once.Arith.SigOp.Builders.W.⊝_
d_'8861'__162 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
d_'8861'__162 v0
  = coe
      MAlonzo.Code.Once.Word.d_'8861'__44
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.Builders.W.⊝-fromℤ
d_'8861''45'fromℤ_164 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'fromℤ_164 = erased
-- Once.Arith.SigOp.Builders.W.⊝-intMin
d_'8861''45'intMin_166 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_166 = erased
-- Once.Arith.SigOp.Builders.W.⊝-invol-norm
d_'8861''45'invol'45'norm_168 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'invol'45'norm_168 = erased
-- Once.Arith.SigOp.Builders.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_172 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_172
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'base'45'to'45'full_786
-- Once.Arith.SigOp.Builders.M.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_174 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_174 = erased
-- Once.Arith.SigOp.Builders.M.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_176 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_176 = erased
-- Once.Arith.SigOp.Builders.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_178 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_178
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'full'45'to'45'base_754
-- Once.Arith.SigOp.Builders.M.coerce-functor
d_coerce'45'functor_180 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor_180 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_250 v0 v2
-- Once.Arith.SigOp.Builders.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_182 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_182 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_292
      v0 v2
-- Once.Arith.SigOp.Builders.M.coerce-round-trip
d_coerce'45'round'45'trip_184 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_184 = erased
-- Once.Arith.SigOp.Builders.M.coerce-struct
d_coerce'45'struct_186 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'struct_186
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct_422
-- Once.Arith.SigOp.Builders.M.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_188 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_188 = erased
-- Once.Arith.SigOp.Builders.M.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_190 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_190
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct'8315''185'_428
-- Once.Arith.SigOp.Builders.M.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_192 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_192 = erased
-- Once.Arith.SigOp.Builders.M.coerce-μ-in
d_coerce'45'μ'45'in_194 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_194 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'in_886 v0 v2
-- Once.Arith.SigOp.Builders.M.coerce-μ-out
d_coerce'45'μ'45'out_196 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_196 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928 v0 v1
      v3
-- Once.Arith.SigOp.Builders.M.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_198 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_198 = erased
-- Once.Arith.SigOp.Builders.M.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_200 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_200 = erased
-- Once.Arith.SigOp.Builders.M.coerce-ν-in
d_coerce'45'ν'45'in_202 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_202
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_1120
-- Once.Arith.SigOp.Builders.M.coerce-ν-out
d_coerce'45'ν'45'out_204 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_204
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'out_1126
-- Once.Arith.SigOp.Builders.M.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_206 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_206 = erased
-- Once.Arith.SigOp.Builders.M.eraseᵍ
d_erase'7501'_208 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_erase'7501'_208
  = coe MAlonzo.Code.Once.Semantics.Value.du_erase'7501'_92
-- Once.Arith.SigOp.Builders.M.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_210 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_210 = erased
-- Once.Arith.SigOp.Builders.M.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_212 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_212 = erased
-- Once.Arith.SigOp.Builders.M.fmap-struct-coherence
d_fmap'45'struct'45'coherence_214 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_214 = erased
-- Once.Arith.SigOp.Builders.M.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_216 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_216 = erased
-- Once.Arith.SigOp.Builders.M.sem-CoIn
d_sem'45'CoIn_218 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'CoIn_218
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoIn_1140
-- Once.Arith.SigOp.Builders.M.sem-CoOut
d_sem'45'CoOut_220 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 ->
  MAlonzo.Code.Once.Res.T_Res_6
d_sem'45'CoOut_220
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoOut_1130
-- Once.Arith.SigOp.Builders.M.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_222 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_222 = erased
-- Once.Arith.SigOp.Builders.M.sem-In
d_sem'45'In_224 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_μS_182
d_sem'45'In_224
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'In_1060
-- Once.Arith.SigOp.Builders.M.sem-In-Out
d_sem'45'In'45'Out_226 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_226 = erased
-- Once.Arith.SigOp.Builders.M.sem-Out
d_sem'45'Out_228 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'Out_228
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'Out_1068
-- Once.Arith.SigOp.Builders.M.sem-Out-In
d_sem'45'Out'45'In_230 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_230 = erased
-- Once.Arith.SigOp.Builders.M.sem-ana
d_sem'45'ana_232 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'ana_232 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'ana_1164 v0 v2 v3
-- Once.Arith.SigOp.Builders.M.sem-case
d_sem'45'case_234 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_234 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'case_486 v3 v4 v5
-- Once.Arith.SigOp.Builders.M.sem-case-inl
d_sem'45'case'45'inl_236 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_236 = erased
-- Once.Arith.SigOp.Builders.M.sem-case-inr
d_sem'45'case'45'inr_238 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_238 = erased
-- Once.Arith.SigOp.Builders.M.sem-cata
d_sem'45'cata_240 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'cata_240 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_1080 v0 v1 v3
-- Once.Arith.SigOp.Builders.M.sem-cata-compute
d_sem'45'cata'45'compute_242 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_242 = erased
-- Once.Arith.SigOp.Builders.M.sem-fmap
d_sem'45'fmap_244 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_244 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_574 v0 v3 v4
-- Once.Arith.SigOp.Builders.M.sem-fmap-Type
d_sem'45'fmap'45'Type_246 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_246 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap'45'Type_618 v0 v3
      v4
-- Once.Arith.SigOp.Builders.M.sem-fst
d_sem'45'fst_248 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_248 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fst_450 v2
-- Once.Arith.SigOp.Builders.M.sem-fst-pair
d_sem'45'fst'45'pair_250 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_250 = erased
-- Once.Arith.SigOp.Builders.M.sem-functor-coherence
d_sem'45'functor'45'coherence_252 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_252 = erased
-- Once.Arith.SigOp.Builders.M.sem-fuseNat
d_sem'45'fuseNat_254 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'fuseNat_254 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat_1314 v0 v1 v2
      v3 v5 v6
-- Once.Arith.SigOp.Builders.M.sem-fuseNat-cong
d_sem'45'fuseNat'45'cong_256 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
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
d_sem'45'fuseNat'45'cong_256 = erased
-- Once.Arith.SigOp.Builders.M.sem-fuseNat-events
d_sem'45'fuseNat'45'events_258 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'fuseNat'45'events_258 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat'45'events_1410
      v1 v2 v3 v4 v5 v6 v8 v9
-- Once.Arith.SigOp.Builders.M.sem-inl
d_sem'45'inl_260 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_260 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inl_472
-- Once.Arith.SigOp.Builders.M.sem-inr
d_sem'45'inr_262 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_262 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inr_478
-- Once.Arith.SigOp.Builders.M.sem-pair
d_sem'45'pair_264 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_264 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'pair_462 v2 v3
-- Once.Arith.SigOp.Builders.M.sem-para
d_sem'45'para_266 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'para_266 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'para_1096 v0 v1 v3 v4
-- Once.Arith.SigOp.Builders.M.sem-snd
d_sem'45'snd_268 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_268 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'snd_456 v2
-- Once.Arith.SigOp.Builders.M.sem-snd-pair
d_sem'45'snd'45'pair_270 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_270 = erased
-- Once.Arith.SigOp.Builders.M.semAnaLayer
d_semAnaLayer_272 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_semAnaLayer_272 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_semAnaLayer_1170 v0 v2 v3
-- Once.Arith.SigOp.Builders.M.sfmapSemAna
d_sfmapSemAna_274 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> AgdaAny
d_sfmapSemAna_274 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sfmapSemAna_1178 v0 v1 v3 v4
-- Once.Arith.SigOp.Builders.M.sfmapSemAna-is-sfmap
d_sfmapSemAna'45'is'45'sfmap_276 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapSemAna'45'is'45'sfmap_276 = erased
-- Once.Arith.SigOp.Builders.M.⟦_⟧
d_'10214'_'10215'_278 :: MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_'10214'_'10215'_278 = erased
-- Once.Arith.SigOp.Builders.M.⟦_⟧F
d_'10214'_'10215'F_280 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> ()
d_'10214'_'10215'F_280 = erased
-- Once.Arith.SigOp.Builders.M.⟦_⟧ᵍ
d_'10214'_'10215''7501'_282 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_'10214'_'10215''7501'_282 = erased
-- Once.Arith.SigOp.Builders.M.⟦μ⟧
d_'10214'μ'10215'_284 :: MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_'10214'μ'10215'_284 = erased
-- Once.Arith.SigOp.Builders.M.⟦ν⟧
d_'10214'ν'10215'_286 :: MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_'10214'ν'10215'_286 = erased
-- Once.Arith.SigOp.Builders.base-I×I
d_base'45'I'215'I_288 ::
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196
d_base'45'I'215'I_288
  = coe
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202)
-- Once.Arith.SigOp.Builders.base-U+U
d_base'45'U'43'U_290 ::
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196
d_base'45'U'43'U_290
  = coe
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_216
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198)
-- Once.Arith.SigOp.Builders.add-info
d_add'45'info_292 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_add'45'info_292
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_186
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.add.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_158
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'add_388))
      (coe d_base'45'I'215'I_288)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202)
-- Once.Arith.SigOp.Builders.sub-info
d_sub'45'info_294 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_sub'45'info_294
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_186
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.sub.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_158
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'sub_390))
      (coe d_base'45'I'215'I_288)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202)
-- Once.Arith.SigOp.Builders.mul-info
d_mul'45'info_296 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_mul'45'info_296
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_186
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.mul.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_158
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'mul_392))
      (coe d_base'45'I'215'I_288)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202)
-- Once.Arith.SigOp.Builders.div-info
d_div'45'info_298 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_div'45'info_298
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_186
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.div.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_158
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'div_394))
      (coe d_base'45'I'215'I_288)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202)
-- Once.Arith.SigOp.Builders.mod-info
d_mod'45'info_300 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_mod'45'info_300
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_186
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.mod.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_158
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'mod_396))
      (coe d_base'45'I'215'I_288)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202)
-- Once.Arith.SigOp.Builders.neg-info
d_neg'45'info_302 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_neg'45'info_302
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_186
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.neg.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_158
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'neg_398))
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202)
-- Once.Arith.SigOp.Builders.base-F×F
d_base'45'F'215'F_304 ::
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196
d_base'45'F'215'F_304
  = coe
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204)
-- Once.Arith.SigOp.Builders.fadd-info
d_fadd'45'info_306 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_fadd'45'info_306
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_186
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.add.float" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_158
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'fadd_400))
      (coe d_base'45'F'215'F_304)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204)
-- Once.Arith.SigOp.Builders.fsub-info
d_fsub'45'info_308 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_fsub'45'info_308
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_186
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.sub.float" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_158
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'fsub_402))
      (coe d_base'45'F'215'F_304)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204)
-- Once.Arith.SigOp.Builders.fmul-info
d_fmul'45'info_310 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_fmul'45'info_310
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_186
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.mul.float" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_158
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'fmul_404))
      (coe d_base'45'F'215'F_304)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204)
-- Once.Arith.SigOp.Builders.fdiv-info
d_fdiv'45'info_312 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_fdiv'45'info_312
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_186
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.div.float" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_158
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'fdiv_406))
      (coe d_base'45'F'215'F_304)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204)
-- Once.Arith.SigOp.Builders.i2f-info
d_i2f'45'info_314 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_i2f'45'info_314
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_186
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.i2f" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_158
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'i2f_408))
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204)
-- Once.Arith.SigOp.Builders.lt-info
d_lt'45'info_316 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_lt'45'info_316
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_186
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.lt.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_158
         (coe
            MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_410
            (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'lt_8)))
      (coe d_base'45'I'215'I_288) (coe d_base'45'U'43'U_290)
-- Once.Arith.SigOp.Builders.le-info
d_le'45'info_318 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_le'45'info_318
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_186
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.le.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_158
         (coe
            MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_410
            (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'le_10)))
      (coe d_base'45'I'215'I_288) (coe d_base'45'U'43'U_290)
-- Once.Arith.SigOp.Builders.gt-info
d_gt'45'info_320 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_gt'45'info_320
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_186
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.gt.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_158
         (coe
            MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_410
            (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'gt_12)))
      (coe d_base'45'I'215'I_288) (coe d_base'45'U'43'U_290)
-- Once.Arith.SigOp.Builders.ge-info
d_ge'45'info_322 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_ge'45'info_322
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_186
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.ge.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_158
         (coe
            MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_410
            (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'ge_14)))
      (coe d_base'45'I'215'I_288) (coe d_base'45'U'43'U_290)
-- Once.Arith.SigOp.Builders.eq-info
d_eq'45'info_324 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_eq'45'info_324
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_186
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.eq.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_158
         (coe
            MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_410
            (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'eq_16)))
      (coe d_base'45'I'215'I_288) (coe d_base'45'U'43'U_290)
-- Once.Arith.SigOp.Builders.ne-info
d_ne'45'info_326 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_ne'45'info_326
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_186
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("arith.ne.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_158
         (coe
            MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_410
            (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'ne_18)))
      (coe d_base'45'I'215'I_288) (coe d_base'45'U'43'U_290)
-- Once.Arith.SigOp.Builders.value-info
d_value'45'info_332 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_value'45'info_332 ~v0 ~v1 v2 v3 v4
  = du_value'45'info_332 v2 v3 v4
du_value'45'info_332 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
du_value'45'info_332 v0 v1 v2
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_186 (coe v0)
      (coe MAlonzo.Code.Once.SigOp.Info.C_ffiV_150) (coe v1) (coe v2)
-- Once.Arith.SigOp.Builders.generic-info
d_generic'45'info_344 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_generic'45'info_344 ~v0 ~v1 = du_generic'45'info_344
du_generic'45'info_344 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
du_generic'45'info_344 = coe du_value'45'info_332
-- Once.Arith.SigOp.Builders.arrow-sem-eff
d_arrow'45'sem'45'eff_350 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142
d_arrow'45'sem'45'eff_350 ~v0 ~v1 v2 v3
  = du_arrow'45'sem'45'eff_350 v2 v3
du_arrow'45'sem'45'eff_350 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142
du_arrow'45'sem'45'eff_350 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3) (coe MAlonzo.Code.Once.SigOp.Info.C_haltsV_156)
             else coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then coe
                                     seq (coe v5) (coe MAlonzo.Code.Once.SigOp.Info.C_emitsV_154)
                              else coe
                                     seq (coe v5) (coe MAlonzo.Code.Once.SigOp.Info.C_callsV_152)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.arrow-sem
d_arrow'45'sem_356 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142
d_arrow'45'sem_356 ~v0 v1 v2 = du_arrow'45'sem_356 v1 v2
du_arrow'45'sem_356 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142
du_arrow'45'sem_356 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_mk'45'kind_50 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_pure_34
               -> coe MAlonzo.Code.Once.SigOp.Info.C_ffiV_150
             MAlonzo.Code.Once.Type.C_eff_36
               -> coe
                    du_arrow'45'sem'45'eff_350
                    (coe MAlonzo.Code.Once.Type.d_isVoid'63'_164 (coe v0))
                    (coe MAlonzo.Code.Once.Type.d_isUnit'63'_168 (coe v0))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.arrow-info
d_arrow'45'info_364 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_arrow'45'info_364 ~v0 v1 v2 v3 v4 v5
  = du_arrow'45'info_364 v1 v2 v3 v4 v5
du_arrow'45'info_364 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
du_arrow'45'info_364 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_186 (coe v2)
      (coe du_arrow'45'sem_356 (coe v0) (coe v1)) (coe v3) (coe v4)
