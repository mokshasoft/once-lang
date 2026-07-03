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

module MAlonzo.Code.Once.Arith.SigOp.Block where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Word

-- Once.Arith.SigOp.Block.W._%ˢ_
d__'37''738'__10 :: Integer -> Integer -> Integer
d__'37''738'__10
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__104 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W._/ˢ_
d__'47''738'__12 :: Integer -> Integer -> Integer
d__'47''738'__12
  = coe MAlonzo.Code.Once.Word.d__'47''738'__98 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W._<ˢ_
d__'60''738'__14 :: Integer -> Integer -> Bool
d__'60''738'__14
  = coe MAlonzo.Code.Once.Word.d__'60''738'__58 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W._≡ʷ_
d__'8801''695'__16 :: Integer -> Integer -> Bool
d__'8801''695'__16 = coe MAlonzo.Code.Once.Word.du__'8801''695'__64
-- Once.Arith.SigOp.Block.W._⊕_
d__'8853'__18 :: Integer -> Integer -> Integer
d__'8853'__18
  = coe MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W._⊖_
d__'8854'__20 :: Integer -> Integer -> Integer
d__'8854'__20
  = coe MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W._⊗_
d__'8855'__22 :: Integer -> Integer -> Integer
d__'8855'__22
  = coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.%ˢ-else
d_'37''738''45'else_24 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_24 = erased
-- Once.Arith.SigOp.Block.W.%ˢ-in-range
d_'37''738''45'in'45'range_26 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_26 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_492
      (coe (64 :: Integer)) v2 v3 v4
-- Once.Arith.SigOp.Block.W.%ˢ-mid
d_'37''738''45'mid_28 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_28 = erased
-- Once.Arith.SigOp.Block.W.%ˢ-negOne
d_'37''738''45'negOne_30 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_30 = erased
-- Once.Arith.SigOp.Block.W.%ˢ-zero
d_'37''738''45'zero_32 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_32 = erased
-- Once.Arith.SigOp.Block.W./ˢ-else
d_'47''738''45'else_34 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_34 = erased
-- Once.Arith.SigOp.Block.W./ˢ-in-range
d_'47''738''45'in'45'range_36 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_36 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_458
      (coe (64 :: Integer)) v2 v3
-- Once.Arith.SigOp.Block.W./ˢ-mid
d_'47''738''45'mid_38 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_38 = erased
-- Once.Arith.SigOp.Block.W./ˢ-negOne
d_'47''738''45'negOne_40 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_40 = erased
-- Once.Arith.SigOp.Block.W./ˢ-zero
d_'47''738''45'zero_42 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_42 = erased
-- Once.Arith.SigOp.Block.W.0<half
d_0'60'half_44 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_44 = coe MAlonzo.Code.Once.Word.du_0'60'half_112
-- Once.Arith.SigOp.Block.W.0<modulus
d_0'60'modulus_46 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_46 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_110
-- Once.Arith.SigOp.Block.W.0<negOne
d_0'60'negOne_48 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_48 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_314 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.2*n≡n+n
d_2'42'n'8801'n'43'n_50 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_50 = erased
-- Once.Arith.SigOp.Block.W.2≤modulus
d_2'8804'modulus_52 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_52 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_310 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.Word
d_Word_54 :: ()
d_Word_54 = erased
-- Once.Arith.SigOp.Block.W.fromℤ
d_fromℤ_56 :: Integer -> Integer
d_fromℤ_56
  = coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.fromℤ-0
d_fromℤ'45'0_58 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_58 = erased
-- Once.Arith.SigOp.Block.W.fromℤ-in-range
d_fromℤ'45'in'45'range_60 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_60
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_118
      (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_62 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_62 = erased
-- Once.Arith.SigOp.Block.W.fromℤ-neg1
d_fromℤ'45'neg1_64 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_64 = erased
-- Once.Arith.SigOp.Block.W.half
d_half_66 :: Integer
d_half_66
  = coe MAlonzo.Code.Once.Word.d_half_48 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.half<modulus
d_half'60'modulus_68 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_68 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_318 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.half≡2^b
d_half'8801'2'94'b_70 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_70 = erased
-- Once.Arith.SigOp.Block.W.half≤negOne
d_half'8804'negOne_72 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_72 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_338
      (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.intMin
d_intMin_74 :: Integer
d_intMin_74
  = coe MAlonzo.Code.Once.Word.d_intMin_54 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.modulus
d_modulus_76 :: Integer
d_modulus_76
  = coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_78 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_78 = erased
-- Once.Arith.SigOp.Block.W.modulus≢0
d_modulus'8802'0_80 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_80
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.mod∸half≡half
d_mod'8760'half'8801'half_82 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_82 = erased
-- Once.Arith.SigOp.Block.W.mod≡half+half
d_mod'8801'half'43'half_84 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_84 = erased
-- Once.Arith.SigOp.Block.W.negOne
d_negOne_86 :: Integer
d_negOne_86
  = coe MAlonzo.Code.Once.Word.d_negOne_56 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.negOne<modulus
d_negOne'60'modulus_88 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_88 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_326
      (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.negOne≢0
d_negOne'8802'0_90 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_90 = erased
-- Once.Arith.SigOp.Block.W.norm
d_norm_92 :: Integer -> Integer
d_norm_92
  = coe MAlonzo.Code.Once.Word.d_norm_16 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.sucNegOne≡mod
d_sucNegOne'8801'mod_94 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_94 = erased
-- Once.Arith.SigOp.Block.W.tdiv-neg1
d_tdiv'45'neg1_96 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_96 = erased
-- Once.Arith.SigOp.Block.W.tmod-neg1
d_tmod'45'neg1_98 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_98 = erased
-- Once.Arith.SigOp.Block.W.toℤ
d_toℤ_100 :: Integer -> Integer
d_toℤ_100
  = coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.toℤ-negOne
d_toℤ'45'negOne_102 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_102 = erased
-- Once.Arith.SigOp.Block.W.≡ᵇ-refl
d_'8801''7495''45'refl_104 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_104 = erased
-- Once.Arith.SigOp.Block.W.≡ᵇ0-false
d_'8801''7495'0'45'false_106 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_106 = erased
-- Once.Arith.SigOp.Block.W.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_108 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_108 = erased
-- Once.Arith.SigOp.Block.W.⊝_
d_'8861'__110 :: Integer -> Integer
d_'8861'__110
  = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.⊝-intMin
d_'8861''45'intMin_112 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_112 = erased
-- Once.Arith.SigOp.Block.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_116 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_116
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'base'45'to'45'full_634
-- Once.Arith.SigOp.Block.M.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_118 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_118 = erased
-- Once.Arith.SigOp.Block.M.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_120 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_120 = erased
-- Once.Arith.SigOp.Block.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_122 ::
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_122
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'full'45'to'45'base_598
-- Once.Arith.SigOp.Block.M.coerce-functor
d_coerce'45'functor_124 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor_124 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_94 v0 v2
-- Once.Arith.SigOp.Block.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_126 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_126 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_136
      v0 v2
-- Once.Arith.SigOp.Block.M.coerce-round-trip
d_coerce'45'round'45'trip_128 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_128 = erased
-- Once.Arith.SigOp.Block.M.coerce-struct
d_coerce'45'struct_130 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct_130
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct_266
-- Once.Arith.SigOp.Block.M.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_132 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_132 = erased
-- Once.Arith.SigOp.Block.M.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_134 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_134
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct'8315''185'_272
-- Once.Arith.SigOp.Block.M.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_136 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_136 = erased
-- Once.Arith.SigOp.Block.M.coerce-μ-in
d_coerce'45'μ'45'in_138 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_138 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'in_746 v0 v2
-- Once.Arith.SigOp.Block.M.coerce-μ-out
d_coerce'45'μ'45'out_140 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_140 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_788 v0 v1
      v3
-- Once.Arith.SigOp.Block.M.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_142 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_142 = erased
-- Once.Arith.SigOp.Block.M.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_144 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_144 = erased
-- Once.Arith.SigOp.Block.M.coerce-ν-in
d_coerce'45'ν'45'in_146 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_146
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_980
-- Once.Arith.SigOp.Block.M.coerce-ν-out
d_coerce'45'ν'45'out_148 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_148
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'out_986
-- Once.Arith.SigOp.Block.M.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_150 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_150 = erased
-- Once.Arith.SigOp.Block.M.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_152 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_152 = erased
-- Once.Arith.SigOp.Block.M.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_154 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_154 = erased
-- Once.Arith.SigOp.Block.M.fmap-struct-coherence
d_fmap'45'struct'45'coherence_156 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_156 = erased
-- Once.Arith.SigOp.Block.M.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_158 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_158 = erased
-- Once.Arith.SigOp.Block.M.sem-CoIn
d_sem'45'CoIn_160 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'CoIn_160
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoIn_1000
-- Once.Arith.SigOp.Block.M.sem-CoOut
d_sem'45'CoOut_162 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 -> AgdaAny
d_sem'45'CoOut_162
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoOut_990
-- Once.Arith.SigOp.Block.M.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_164 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_164 = erased
-- Once.Arith.SigOp.Block.M.sem-In
d_sem'45'In_166 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_μS_182
d_sem'45'In_166
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'In_920
-- Once.Arith.SigOp.Block.M.sem-In-Out
d_sem'45'In'45'Out_168 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_168 = erased
-- Once.Arith.SigOp.Block.M.sem-Out
d_sem'45'Out_170 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'Out_170
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'Out_928
-- Once.Arith.SigOp.Block.M.sem-Out-In
d_sem'45'Out'45'In_172 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_172 = erased
-- Once.Arith.SigOp.Block.M.sem-ana
d_sem'45'ana_174 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'ana_174 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'ana_1024 v0 v2 v3
-- Once.Arith.SigOp.Block.M.sem-case
d_sem'45'case_176 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_176 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'case_330 v3 v4 v5
-- Once.Arith.SigOp.Block.M.sem-case-inl
d_sem'45'case'45'inl_178 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_178 = erased
-- Once.Arith.SigOp.Block.M.sem-case-inr
d_sem'45'case'45'inr_180 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_180 = erased
-- Once.Arith.SigOp.Block.M.sem-cata
d_sem'45'cata_182 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'cata_182 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_940 v0 v1 v3
-- Once.Arith.SigOp.Block.M.sem-cata-compute
d_sem'45'cata'45'compute_184 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_184 = erased
-- Once.Arith.SigOp.Block.M.sem-fmap
d_sem'45'fmap_186 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_186 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_418 v0 v3 v4
-- Once.Arith.SigOp.Block.M.sem-fmap-Type
d_sem'45'fmap'45'Type_188 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_188 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap'45'Type_462 v0 v3
      v4
-- Once.Arith.SigOp.Block.M.sem-fst
d_sem'45'fst_190 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_190 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fst_294 v2
-- Once.Arith.SigOp.Block.M.sem-fst-pair
d_sem'45'fst'45'pair_192 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_192 = erased
-- Once.Arith.SigOp.Block.M.sem-functor-coherence
d_sem'45'functor'45'coherence_194 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_194 = erased
-- Once.Arith.SigOp.Block.M.sem-fuseNat
d_sem'45'fuseNat_196 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'fuseNat_196 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat_1154 v0 v1 v2
      v3 v5 v6
-- Once.Arith.SigOp.Block.M.sem-fuseNat-cong
d_sem'45'fuseNat'45'cong_198 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
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
d_sem'45'fuseNat'45'cong_198 = erased
-- Once.Arith.SigOp.Block.M.sem-fuseNat-events
d_sem'45'fuseNat'45'events_200 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'fuseNat'45'events_200 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat'45'events_1250
      v1 v2 v3 v4 v5 v6 v8 v9
-- Once.Arith.SigOp.Block.M.sem-inl
d_sem'45'inl_202 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_202 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inl_316
-- Once.Arith.SigOp.Block.M.sem-inr
d_sem'45'inr_204 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_204 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inr_322
-- Once.Arith.SigOp.Block.M.sem-pair
d_sem'45'pair_206 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_206 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'pair_306 v2 v3
-- Once.Arith.SigOp.Block.M.sem-para
d_sem'45'para_208 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'para_208 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'para_956 v0 v1 v3 v4
-- Once.Arith.SigOp.Block.M.sem-snd
d_sem'45'snd_210 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_210 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'snd_300 v2
-- Once.Arith.SigOp.Block.M.sem-snd-pair
d_sem'45'snd'45'pair_212 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_212 = erased
-- Once.Arith.SigOp.Block.M.sfmapSemAna
d_sfmapSemAna_214 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmapSemAna_214 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sfmapSemAna_1032 v0 v1 v3 v4
-- Once.Arith.SigOp.Block.M.sfmapSemAna-is-sfmap
d_sfmapSemAna'45'is'45'sfmap_216 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapSemAna'45'is'45'sfmap_216 = erased
-- Once.Arith.SigOp.Block.M.⟦_⟧
d_'10214'_'10215'_218 :: MAlonzo.Code.Once.Type.T_Type_112 -> ()
d_'10214'_'10215'_218 = erased
-- Once.Arith.SigOp.Block.M.⟦_⟧F
d_'10214'_'10215'F_220 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> ()
d_'10214'_'10215'F_220 = erased
-- Once.Arith.SigOp.Block.M.⟦μ⟧
d_'10214'μ'10215'_222 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'μ'10215'_222 = erased
-- Once.Arith.SigOp.Block.M.⟦ν⟧
d_'10214'ν'10215'_224 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'ν'10215'_224 = erased
-- Once.Arith.SigOp.Block.show-side
d_show'45'side_226 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'side_226 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_24
        -> coe ("F" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_26
        -> coe ("S" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.show-path
d_show'45'path_228 ::
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'path_228 v0
  = case coe v0 of
      [] -> coe ("Z" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_show'45'side_226 (coe v1)) (d_show'45'path_228 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.show-zlit
d_show'45'zlit_234 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'zlit_234 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
            ("_" :: Data.Text.Text)
      _ -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("n" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe
                   MAlonzo.Code.Data.Nat.Show.d_show_56
                   (subInt (coe (0 :: Integer)) (coe v0)))
                ("_" :: Data.Text.Text))
-- Once.Arith.SigOp.Block.show-arith-ir
d_show'45'arith'45'ir_242 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'arith'45'ir_242 ~v0 v1 = du_show'45'arith'45'ir_242 v1
du_show'45'arith'45'ir_242 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_show'45'arith'45'ir_242 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("L" :: Data.Text.Text) (d_show'45'zlit_234 (coe v1))
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_16 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("I" :: Data.Text.Text) (d_show'45'path_228 (coe v1))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_18 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("A" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_show'45'arith'45'ir_242 (coe v1))
                (coe du_show'45'arith'45'ir_242 (coe v2)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_20 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("B" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_show'45'arith'45'ir_242 (coe v1))
                (coe du_show'45'arith'45'ir_242 (coe v2)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_22 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("M" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_show'45'arith'45'ir_242 (coe v1))
                (coe du_show'45'arith'45'ir_242 (coe v2)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_24 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("D" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_show'45'arith'45'ir_242 (coe v1))
                (coe du_show'45'arith'45'ir_242 (coe v2)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_26 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("R" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_show'45'arith'45'ir_242 (coe v1))
                (coe du_show'45'arith'45'ir_242 (coe v2)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_28 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("G" :: Data.Text.Text) (coe du_show'45'arith'45'ir_242 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.block-digest
d_block'45'digest_272 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_block'45'digest_272 ~v0 v1 = du_block'45'digest_272 v1
du_block'45'digest_272 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_block'45'digest_272 v0 = coe du_show'45'arith'45'ir_242 (coe v0)
-- Once.Arith.SigOp.Block.block-name
d_block'45'name_278 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_block'45'name_278 ~v0 v1 = du_block'45'name_278 v1
du_block'45'name_278 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_block'45'name_278 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("arith.block." :: Data.Text.Text)
      (coe du_block'45'digest_272 (coe v0))
-- Once.Arith.SigOp.Block.projectM
d_projectM_284 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  AgdaAny -> Maybe Integer
d_projectM_284 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'unit_10
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12
        -> case coe v1 of
             [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             (:) v3 v4 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_14 v3 v4
        -> case coe v1 of
             [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             (:) v5 v6
               -> case coe v5 of
                    MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_24
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> coe d_projectM_284 (coe v3) (coe v6) (coe v7)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_26
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> coe d_projectM_284 (coe v4) (coe v6) (coe v8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.maybe-zeroM
d_maybe'45'zeroM_300 :: Maybe Integer -> Integer
d_maybe'45'zeroM_300 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.block-semM
d_block'45'semM_306 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> Integer
d_block'45'semM_306 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v3
        -> coe
             MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer)) (coe v3)
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_16 v3
        -> coe
             d_maybe'45'zeroM_300
             (coe d_projectM_284 (coe v0) (coe v3) (coe v2))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_18 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer))
             (coe d_block'45'semM_306 (coe v0) (coe v3) (coe v2))
             (coe d_block'45'semM_306 (coe v0) (coe v4) (coe v2))
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_20 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
             (coe d_block'45'semM_306 (coe v0) (coe v3) (coe v2))
             (coe d_block'45'semM_306 (coe v0) (coe v4) (coe v2))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_22 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'8855'__38 (coe (64 :: Integer))
             (coe d_block'45'semM_306 (coe v0) (coe v3) (coe v2))
             (coe d_block'45'semM_306 (coe v0) (coe v4) (coe v2))
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_24 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'47''738'__98 (coe (64 :: Integer))
             (coe d_block'45'semM_306 (coe v0) (coe v3) (coe v2))
             (coe d_block'45'semM_306 (coe v0) (coe v4) (coe v2))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_26 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'37''738'__104 (coe (64 :: Integer))
             (coe d_block'45'semM_306 (coe v0) (coe v3) (coe v2))
             (coe d_block'45'semM_306 (coe v0) (coe v4) (coe v2))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_28 v3
        -> coe
             MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
             (coe d_block'45'semM_306 (coe v0) (coe v3) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.block-info
d_block'45'info_352 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_150
d_block'45'info_352 v0 v1
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_216
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe du_block'45'name_278 (coe v1)))
      (coe d_block'45'semM_306 (coe v0) (coe v1))
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
