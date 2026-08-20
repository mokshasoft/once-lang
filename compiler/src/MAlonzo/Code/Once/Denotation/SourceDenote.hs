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

module MAlonzo.Code.Once.Denotation.SourceDenote where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.SigOp.Builders
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceDenote
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Word

-- Once.Denotation.SourceDenote.IntW._%ˢ_
d__'37''738'__8 :: Integer -> Integer -> Integer
d__'37''738'__8
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__104 (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW._/ˢ_
d__'47''738'__10 :: Integer -> Integer -> Integer
d__'47''738'__10
  = coe MAlonzo.Code.Once.Word.d__'47''738'__98 (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW._<ˢ_
d__'60''738'__12 :: Integer -> Integer -> Bool
d__'60''738'__12
  = coe MAlonzo.Code.Once.Word.d__'60''738'__58 (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW._≡ʷ_
d__'8801''695'__14 :: Integer -> Integer -> Bool
d__'8801''695'__14 = coe MAlonzo.Code.Once.Word.du__'8801''695'__64
-- Once.Denotation.SourceDenote.IntW._⊕_
d__'8853'__16 :: Integer -> Integer -> Integer
d__'8853'__16
  = coe MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW._⊖_
d__'8854'__18 :: Integer -> Integer -> Integer
d__'8854'__18
  = coe MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW._⊗_
d__'8855'__20 :: Integer -> Integer -> Integer
d__'8855'__20
  = coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW.%ˢ-else
d_'37''738''45'else_22 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_22 = erased
-- Once.Denotation.SourceDenote.IntW.%ˢ-in-range
d_'37''738''45'in'45'range_24 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_24 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_526
      (coe (64 :: Integer)) v2 v3 v4
-- Once.Denotation.SourceDenote.IntW.%ˢ-mid
d_'37''738''45'mid_26 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_26 = erased
-- Once.Denotation.SourceDenote.IntW.%ˢ-negOne
d_'37''738''45'negOne_28 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_28 = erased
-- Once.Denotation.SourceDenote.IntW.%ˢ-zero
d_'37''738''45'zero_30 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_30 = erased
-- Once.Denotation.SourceDenote.IntW./ˢ-else
d_'47''738''45'else_32 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_32 = erased
-- Once.Denotation.SourceDenote.IntW./ˢ-in-range
d_'47''738''45'in'45'range_34 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_34 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_492
      (coe (64 :: Integer)) v2 v3
-- Once.Denotation.SourceDenote.IntW./ˢ-mid
d_'47''738''45'mid_36 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_36 = erased
-- Once.Denotation.SourceDenote.IntW./ˢ-negOne
d_'47''738''45'negOne_38 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_38 = erased
-- Once.Denotation.SourceDenote.IntW./ˢ-pow2
d_'47''738''45'pow2_40 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_40 = erased
-- Once.Denotation.SourceDenote.IntW./ˢ-zero
d_'47''738''45'zero_42 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_42 = erased
-- Once.Denotation.SourceDenote.IntW.0<half
d_0'60'half_44 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_44 = coe MAlonzo.Code.Once.Word.du_0'60'half_146
-- Once.Denotation.SourceDenote.IntW.0<modulus
d_0'60'modulus_46 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_46 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_144
-- Once.Denotation.SourceDenote.IntW.0<negOne
d_0'60'negOne_48 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_48 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_348 (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW.1<modulus
d_1'60'modulus_50 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_50
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_628 (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW.2*n≡n+n
d_2'42'n'8801'n'43'n_52 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_52 = erased
-- Once.Denotation.SourceDenote.IntW.2≤modulus
d_2'8804'modulus_54 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_54 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_344 (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW.Word
d_Word_56 :: ()
d_Word_56 = erased
-- Once.Denotation.SourceDenote.IntW.fromℤ
d_fromℤ_58 :: Integer -> Integer
d_fromℤ_58
  = coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW.fromℤ-0
d_fromℤ'45'0_60 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_60 = erased
-- Once.Denotation.SourceDenote.IntW.fromℤ-in-range
d_fromℤ'45'in'45'range_62 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_62
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_152
      (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_64 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_64 = erased
-- Once.Denotation.SourceDenote.IntW.fromℤ-neg1
d_fromℤ'45'neg1_66 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_66 = erased
-- Once.Denotation.SourceDenote.IntW.half
d_half_68 :: Integer
d_half_68
  = coe MAlonzo.Code.Once.Word.d_half_48 (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW.half<modulus
d_half'60'modulus_70 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_70 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_352 (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW.half≡2^b
d_half'8801'2'94'b_72 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_72 = erased
-- Once.Denotation.SourceDenote.IntW.half≤negOne
d_half'8804'negOne_74 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_74 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_372
      (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW.intMin
d_intMin_76 :: Integer
d_intMin_76
  = coe MAlonzo.Code.Once.Word.d_intMin_54 (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW.modulus
d_modulus_78 :: Integer
d_modulus_78
  = coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_80 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_80 = erased
-- Once.Denotation.SourceDenote.IntW.modulus≢0
d_modulus'8802'0_82 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_82
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW.mod∸half≡half
d_mod'8760'half'8801'half_84 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_84 = erased
-- Once.Denotation.SourceDenote.IntW.mod≡half+half
d_mod'8801'half'43'half_86 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_86 = erased
-- Once.Denotation.SourceDenote.IntW.negOne
d_negOne_88 :: Integer
d_negOne_88
  = coe MAlonzo.Code.Once.Word.d_negOne_56 (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW.negOne<modulus
d_negOne'60'modulus_90 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_90 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_360
      (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW.negOne≢0
d_negOne'8802'0_92 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_92 = erased
-- Once.Denotation.SourceDenote.IntW.norm
d_norm_94 :: Integer -> Integer
d_norm_94
  = coe MAlonzo.Code.Once.Word.d_norm_16 (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW.norm-0
d_norm'45'0_96 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_96 = erased
-- Once.Denotation.SourceDenote.IntW.norm-id
d_norm'45'id_98 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_98 = erased
-- Once.Denotation.SourceDenote.IntW.sdiv2ᵏ
d_sdiv2'7503'_100 :: Integer -> Integer -> Integer
d_sdiv2'7503'_100
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_116 (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW.shlᵂ
d_shl'7490'_102 :: Integer -> Integer -> Integer
d_shl'7490'_102
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_110 (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW.sucNegOne≡mod
d_sucNegOne'8801'mod_104 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_104 = erased
-- Once.Denotation.SourceDenote.IntW.tdiv-neg1
d_tdiv'45'neg1_106 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_106 = erased
-- Once.Denotation.SourceDenote.IntW.tmod-neg1
d_tmod'45'neg1_108 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_108 = erased
-- Once.Denotation.SourceDenote.IntW.toℤ
d_toℤ_110 :: Integer -> Integer
d_toℤ_110
  = coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW.toℤ-negOne
d_toℤ'45'negOne_112 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_112 = erased
-- Once.Denotation.SourceDenote.IntW.≡ᵇ-refl
d_'8801''7495''45'refl_114 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_114 = erased
-- Once.Denotation.SourceDenote.IntW.≡ᵇ0-false
d_'8801''7495'0'45'false_116 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_116 = erased
-- Once.Denotation.SourceDenote.IntW.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_118 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_118 = erased
-- Once.Denotation.SourceDenote.IntW.⊕-neg
d_'8853''45'neg_120 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_120 = erased
-- Once.Denotation.SourceDenote.IntW.⊕-neg-suc
d_'8853''45'neg'45'suc_122 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_122 = erased
-- Once.Denotation.SourceDenote.IntW.⊕-normʳ
d_'8853''45'norm'691'_124 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_124 = erased
-- Once.Denotation.SourceDenote.IntW.⊕≡+
d_'8853''8801''43'_126 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_126 = erased
-- Once.Denotation.SourceDenote.IntW.⊖-normʳ
d_'8854''45'norm'691'_128 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_128 = erased
-- Once.Denotation.SourceDenote.IntW.⊖≡∸
d_'8854''8801''8760'_130 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_130 = erased
-- Once.Denotation.SourceDenote.IntW.⊗-pow2
d_'8855''45'pow2_132 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_132 = erased
-- Once.Denotation.SourceDenote.IntW.⊝_
d_'8861'__134 :: Integer -> Integer
d_'8861'__134
  = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
-- Once.Denotation.SourceDenote.IntW.⊝-intMin
d_'8861''45'intMin_136 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_136 = erased
-- Once.Denotation.SourceDenote.lookupᴰ
d_lookup'7472'_144 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> AgdaAny
d_lookup'7472'_144 ~v0 v1 v2 v3 = du_lookup'7472'_144 v1 v2 v3
du_lookup'7472'_144 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> AgdaAny
du_lookup'7472'_144 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v4 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v8
               -> coe
                    du_lookup'7472'_144 (coe v4) (coe v8)
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.SourceDenote.cata-ev-algˢ
d_cata'45'ev'45'alg'738'_168 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'ev'45'alg'738'_168 v0 ~v1 v2 v3 v4
  = du_cata'45'ev'45'alg'738'_168 v0 v2 v3 v4
du_cata'45'ev'45'alg'738'_168 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cata'45'ev'45'alg'738'_168 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            MAlonzo.Code.Once.Denotation.TraceDenote.du_events'45'F_10 (coe v0)
            (coe (\ v4 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
            (coe v3))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_62
            (coe du_step_186 (coe v0) (coe v2) (coe v3)) (coe v1)))
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
         (coe du_step_186 (coe v0) (coe v2) (coe v3)) (coe v1))
-- Once.Denotation.SourceDenote._.z
d_z_184 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> AgdaAny
d_z_184 v0 ~v1 ~v2 ~v3 v4 = du_z_184 v0 v4
du_z_184 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> AgdaAny -> AgdaAny
du_z_184 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_184
      (coe v0)
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_420 (coe v0)
         (coe (\ v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
         (coe v1))
-- Once.Denotation.SourceDenote._.step
d_step_186 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_186 v0 ~v1 ~v2 v3 v4 = du_step_186 v0 v3 v4
du_step_186 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_186 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
      (coe v1) (coe (\ v3 -> coe v3 (coe du_z_184 (coe v0) (coe v2))))
-- Once.Denotation.SourceDenote.ana-eventsˢ
d_ana'45'events'738'_194 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_ana'45'events'738'_194 v0 v1 v2 v3 v4
  = case coe v4 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v5 = subInt (coe v4) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_62
                   (coe du_step_214 (coe v1) (coe v2) (coe v3)) (coe v5))
                (coe
                   MAlonzo.Code.Once.Denotation.TraceDenote.du_events'45'F_10 (coe v0)
                   (coe
                      (\ v6 ->
                         d_ana'45'events'738'_194
                           (coe v0) (coe v1) (coe v2) (coe v6) (coe v5)))
                   (coe d_layer_218 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))))
-- Once.Denotation.SourceDenote._.step
d_step_214 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_214 ~v0 v1 v2 v3 ~v4 = du_step_214 v1 v2 v3
du_step_214 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_214 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
      (coe v1)
      (coe
         (\ v3 ->
            coe
              v3
              (MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60
                 (coe v0) (coe v2))))
-- Once.Denotation.SourceDenote._.layer
d_layer_218 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> Integer -> AgdaAny
d_layer_218 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_96 (coe v0)
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
         (coe
            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
            (coe du_step_214 (coe v1) (coe v2) (coe v3)) (coe v4)))
-- Once.Denotation.SourceDenote.liftD
d_liftD_228 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_liftD_228 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_404 (coe v0)
         (coe v1) (coe v2) (coe v3))
-- Once.Denotation.SourceDenote.⟦_⟧ˢ
d_'10214'_'10215''738'_246 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214'_'10215''738'_246 ~v0 v1 ~v2 v3 v4 v5 v6
  = du_'10214'_'10215''738'_246 v1 v3 v4 v5 v6
du_'10214'_'10215''738'_246 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214'_'10215''738'_246 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_16 v7
        -> coe
             (\ v8 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe du_lookup'7472'_144 (coe v0) (coe v7) (coe v4)))
      MAlonzo.Code.Once.Surface.Syntax.C_lam_32 v8 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v14 v15 v16
               -> coe
                    (\ v17 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                         (coe
                            (\ v18 ->
                               coe
                                 du_'10214'_'10215''738'_246
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0)
                                    (coe v14))
                                 (coe v16) (coe v13) (coe v3)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                                    (coe v18)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_48 v7 v8 v9 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_246 (coe v0)
                (coe
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v9)
                   (coe
                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v11)
                      (coe MAlonzo.Code.Once.Type.C_pure_34))
                   (coe v1))
                (coe v12) (coe v3) (coe v4))
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                (coe
                   du_'10214'_'10215''738'_246 (coe v0) (coe v9) (coe v13) (coe v3)
                   (coe v4)))
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_62 v7 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v13 v14 v15
               -> coe
                    (\ v16 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                         (coe
                            (\ v17 ->
                               coe
                                 MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                 (coe
                                    du_'10214'_'10215''738'_246 (coe v0)
                                    (coe
                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v9)
                                       (coe
                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                          (coe MAlonzo.Code.Once.Type.C_eff_36))
                                       (coe v15))
                                    (coe v11) (coe v3) (coe v4))
                                 (coe
                                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                    (coe
                                       du_'10214'_'10215''738'_246 (coe v0) (coe v9) (coe v12)
                                       (coe v3) (coe v4))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_76 v7 v8 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__126 v13 v14
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                    (coe
                       du_'10214'_'10215''738'_246 (coe v0) (coe v13) (coe v11) (coe v3)
                       (coe v4))
                    (coe
                       (\ v15 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                            (coe
                               du_'10214'_'10215''738'_246 (coe v0) (coe v14) (coe v12) (coe v3)
                               (coe v4))
                            (coe
                               (\ v16 v17 ->
                                  coe
                                    MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v15)
                                       (coe v16))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_88 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_246 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v1) (coe v9))
                (coe v10) (coe v3) (coe v4))
             (coe
                (\ v11 v12 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v11))))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_100 v8 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_246 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v8) (coe v1))
                (coe v10) (coe v3) (coe v4))
             (coe
                (\ v11 v12 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v11))))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_112 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__128 v11 v12
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                    (coe
                       du_'10214'_'10215''738'_246 (coe v0) (coe v11) (coe v10) (coe v3)
                       (coe v4))
                    (coe
                       (\ v13 v14 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v13))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_124 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__128 v11 v12
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                    (coe
                       du_'10214'_'10215''738'_246 (coe v0) (coe v12) (coe v10) (coe v3)
                       (coe v4))
                    (coe
                       (\ v13 v14 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v13))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_146 v7 v8 v9 v10 v11 v12 v13 v15 v16 v17
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_246 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'43'__128 (coe v12) (coe v13))
                (coe v15) (coe v3) (coe v4))
             (coe
                MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                (\ v18 ->
                   coe
                     du_'10214'_'10215''738'_246
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v12))
                     (coe v1) (coe v16) (coe v3)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v18)))
                (\ v18 ->
                   coe
                     du_'10214'_'10215''738'_246
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v13))
                     (coe v1) (coe v17) (coe v3)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v18))))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_152
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_162 v9
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_246 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Void_124) (coe v9) (coe v3) (coe v4))
             (\ v10 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      MAlonzo.Code.Once.Surface.Syntax.C_let''_178 v7 v8 v9 v10 v12 v13
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_246 (coe v0) (coe v10) (coe v12) (coe v3)
                (coe v4))
             (coe
                (\ v14 ->
                   coe
                     du_'10214'_'10215''738'_246
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v10))
                     (coe v1) (coe v13) (coe v3)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v14))))
      MAlonzo.Code.Once.Surface.Syntax.C_int_184 v7
        -> coe
             (\ v8 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe
                     MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer)) (coe v7)))
      MAlonzo.Code.Once.Surface.Syntax.C_str_190 v7
        -> coe
             (\ v8 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe
                     MAlonzo.Code.Once.SigOp.Info.du_semM_188
                     (MAlonzo.Code.Once.Arith.SigOp.Builders.d_str'45'lit'45'info_324
                        (coe v7))
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Surface.Syntax.C_float_198 v7 v8
        -> coe
             (\ v9 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe
                     MAlonzo.Code.Once.Float.Dyadic.d_encode_140 (coe v3) (coe v7)))
      MAlonzo.Code.Once.Surface.Syntax.C_add_208 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_246 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3) (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_246 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v3) (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_300
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_218 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_246 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3) (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_246 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v3) (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_302
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_228 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_246 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3) (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_246 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v3) (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_304
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_div_238 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_246 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3) (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_246 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v3) (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_306
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_248 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_246 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3) (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_246 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v3) (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_308
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_256 v8
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_246 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3) (coe v4))
             (coe
                (\ v9 v10 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                     (coe
                        MAlonzo.Code.Once.SigOp.Info.du_semM_188
                        MAlonzo.Code.Once.Arith.SigOp.Builders.d_neg'45'info_310 v9)))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_266 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_246 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3) (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_246 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v3) (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_312
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_le_276 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_246 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3) (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_246 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v3) (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_314
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_286 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_246 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3) (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_246 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v3) (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_316
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_296 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_246 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3) (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_246 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v3) (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_318
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_306 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_246 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3) (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_246 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v3) (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_320
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_316 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_246 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3) (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_246 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v3) (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_322
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_arr''_328 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v11 v12 v13
               -> coe
                    du_'10214'_'10215''738'_246 (coe v0)
                    (coe MAlonzo.Code.Once.Type.d__'8658'__150 (coe v11) (coe v13))
                    (coe v10) (coe v3) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_336 v8 v9
        -> let v10
                 = \ v10 ->
                     coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.du_emit'45'D_158
                          (coe MAlonzo.Code.Once.Type.C_Unit_122)
                          (coe
                             MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_338
                             (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v1) (coe v8)
                             (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)
                             (coe v9))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60 (coe v1)
                          (coe
                             MAlonzo.Code.Once.SigOp.Info.du_semM_188
                             (MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_338
                                (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v1) (coe v8)
                                (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)
                                (coe v9))
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v11 v12 v13
                  -> case coe v9 of
                       MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v17 v18
                         -> coe
                              (\ v19 ->
                                 coe
                                   MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                   (coe
                                      (\ v20 v21 ->
                                         coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe
                                              MAlonzo.Code.Once.Denotation.ValueDomain.du_emit'45'D_158
                                              (coe v11)
                                              (coe
                                                 MAlonzo.Code.Once.Arith.SigOp.Builders.d_arrow'45'info_380
                                                 (coe v11) (coe v13) (coe v12) (coe v8) (coe v17)
                                                 (coe v18))
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
                                                 (coe v11) (coe v20)))
                                           (coe
                                              MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60
                                              (coe v13)
                                              (coe
                                                 MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                                 (MAlonzo.Code.Once.Arith.SigOp.Builders.d_arrow'45'info_380
                                                    (coe v11) (coe v13) (coe v12) (coe v8) (coe v17)
                                                    (coe v18))
                                                 (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
                                                    (coe v11) (coe v20)))))))
                       _ -> coe v10
                _ -> coe v10)
      MAlonzo.Code.Once.Surface.Syntax.C_closure_344 v8
        -> coe
             (\ v9 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Denotation.ValueDomain.du_emit'45'D_158
                     (coe MAlonzo.Code.Once.Type.C_Unit_122)
                     (coe
                        MAlonzo.Code.Once.Arith.SigOp.Builders.d_internal'45'info_348
                        (coe v1) (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v8)))
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                  (coe
                     MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60 (coe v1)
                     (coe
                        MAlonzo.Code.Once.SigOp.Info.du_semM_188
                        (MAlonzo.Code.Once.Arith.SigOp.Builders.d_internal'45'info_348
                           (coe v1) (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v8)))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      MAlonzo.Code.Once.Surface.Syntax.C_poly_354 v7
        -> coe
             (\ v9 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Denotation.ValueDomain.du_emit'45'D_158
                     (coe MAlonzo.Code.Once.Type.C_Unit_122)
                     (coe
                        MAlonzo.Code.Once.Arith.SigOp.Builders.d_internal'45'info_348
                        (coe v1) (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v7)))
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                  (coe
                     MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60 (coe v1)
                     (coe
                        MAlonzo.Code.Once.SigOp.Info.du_semM_188
                        (MAlonzo.Code.Once.Arith.SigOp.Builders.d_internal'45'info_348
                           (coe v1) (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v7)))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_366 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v11 v12 v13
               -> coe d_liftD_228 (coe v3) (coe v11) (coe v13) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_378 v7 v8 v10 v11
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_246 (coe v0) (coe v8) (coe v11) (coe v3)
                (coe v4))
             (coe
                (\ v12 ->
                   MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12
                     (coe v3) (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v8))
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v1)) (coe v10)
                     (coe v12)))
      MAlonzo.Code.Once.Surface.Syntax.C_cata_390 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v12 v13 v14
               -> case coe v12 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v15
                      -> case coe v13 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v16 v17
                             -> coe
                                  (\ v18 ->
                                     coe
                                       MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                       (coe
                                          (\ v19 v20 ->
                                             coe
                                               MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_942
                                               v15 v10
                                               (coe
                                                  du_cata'45'ev'45'alg'738'_168 (coe v15) (coe v20)
                                                  (coe
                                                     du_'10214'_'10215''738'_246
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                     (coe
                                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                        (coe
                                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                           (coe v15) (coe v14))
                                                        (coe
                                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                           (coe v17))
                                                        (coe v14))
                                                     (coe v11) (coe v3)
                                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                               v19)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_402 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v12 v13 v14
               -> case coe v13 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                      -> case coe v14 of
                           MAlonzo.Code.Once.Type.C_ν'45'type_134 v17
                             -> coe
                                  (\ v18 ->
                                     coe
                                       MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                       (coe
                                          (\ v19 v20 ->
                                             coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  d_ana'45'events'738'_194 (coe v17) (coe v12)
                                                  (coe
                                                     du_'10214'_'10215''738'_246
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                     (coe
                                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                        (coe v12)
                                                        (coe
                                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                           (coe v16))
                                                        (coe
                                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                           (coe v17) (coe v12)))
                                                     (coe v11) (coe v3)
                                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                  (coe
                                                     MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
                                                     (coe v12) (coe v19))
                                                  (coe v20))
                                               (coe
                                                  MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60
                                                  (coe v14)
                                                  (coe
                                                     MAlonzo.Code.Once.Semantics.Value.du_sem'45'ana_1026
                                                     (coe v17)
                                                     (coe
                                                        (\ v21 ->
                                                           coe
                                                             MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_96
                                                             (coe v17)
                                                             (coe
                                                                MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                                   (coe v17) (coe v12))
                                                                (coe
                                                                   MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                                                   (coe
                                                                      MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                                                      (coe
                                                                         du_'10214'_'10215''738'_246
                                                                         (coe
                                                                            MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                                            (coe v12)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C_Many_10)
                                                                               (coe v16))
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                                               (coe v17) (coe v12)))
                                                                         (coe v11) (coe v3)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                      (0 :: Integer)
                                                                      (MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60
                                                                         (coe v12) (coe v21)))
                                                                   (coe (0 :: Integer))))))
                                                     (coe
                                                        MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
                                                        (coe v12) (coe v19)))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
