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

module MAlonzo.Code.Once.Surface.Elaborate where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Arith.SigOp.Builders
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Word

-- Once.Surface.Elaborate.IntW._%ˢ_
d__'37''738'__8 :: Integer -> Integer -> Integer
d__'37''738'__8
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__104 (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW._/ˢ_
d__'47''738'__10 :: Integer -> Integer -> Integer
d__'47''738'__10
  = coe MAlonzo.Code.Once.Word.d__'47''738'__98 (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW._<ˢ_
d__'60''738'__12 :: Integer -> Integer -> Bool
d__'60''738'__12
  = coe MAlonzo.Code.Once.Word.d__'60''738'__58 (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW._≡ʷ_
d__'8801''695'__14 :: Integer -> Integer -> Bool
d__'8801''695'__14 = coe MAlonzo.Code.Once.Word.du__'8801''695'__64
-- Once.Surface.Elaborate.IntW._⊕_
d__'8853'__16 :: Integer -> Integer -> Integer
d__'8853'__16
  = coe MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW._⊖_
d__'8854'__18 :: Integer -> Integer -> Integer
d__'8854'__18
  = coe MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW._⊗_
d__'8855'__20 :: Integer -> Integer -> Integer
d__'8855'__20
  = coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW.%ˢ-else
d_'37''738''45'else_22 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_22 = erased
-- Once.Surface.Elaborate.IntW.%ˢ-in-range
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
-- Once.Surface.Elaborate.IntW.%ˢ-mid
d_'37''738''45'mid_26 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_26 = erased
-- Once.Surface.Elaborate.IntW.%ˢ-negOne
d_'37''738''45'negOne_28 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_28 = erased
-- Once.Surface.Elaborate.IntW.%ˢ-zero
d_'37''738''45'zero_30 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_30 = erased
-- Once.Surface.Elaborate.IntW./ˢ-else
d_'47''738''45'else_32 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_32 = erased
-- Once.Surface.Elaborate.IntW./ˢ-in-range
d_'47''738''45'in'45'range_34 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_34 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_492
      (coe (64 :: Integer)) v2 v3
-- Once.Surface.Elaborate.IntW./ˢ-mid
d_'47''738''45'mid_36 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_36 = erased
-- Once.Surface.Elaborate.IntW./ˢ-negOne
d_'47''738''45'negOne_38 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_38 = erased
-- Once.Surface.Elaborate.IntW./ˢ-pow2
d_'47''738''45'pow2_40 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_40 = erased
-- Once.Surface.Elaborate.IntW./ˢ-zero
d_'47''738''45'zero_42 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_42 = erased
-- Once.Surface.Elaborate.IntW.0<half
d_0'60'half_44 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_44 = coe MAlonzo.Code.Once.Word.du_0'60'half_146
-- Once.Surface.Elaborate.IntW.0<modulus
d_0'60'modulus_46 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_46 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_144
-- Once.Surface.Elaborate.IntW.0<negOne
d_0'60'negOne_48 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_48 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_348 (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW.1<modulus
d_1'60'modulus_50 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_50
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_628 (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW.2*n≡n+n
d_2'42'n'8801'n'43'n_52 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_52 = erased
-- Once.Surface.Elaborate.IntW.2≤modulus
d_2'8804'modulus_54 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_54 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_344 (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW.Word
d_Word_56 :: ()
d_Word_56 = erased
-- Once.Surface.Elaborate.IntW.fromℤ
d_fromℤ_58 :: Integer -> Integer
d_fromℤ_58
  = coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW.fromℤ-0
d_fromℤ'45'0_60 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_60 = erased
-- Once.Surface.Elaborate.IntW.fromℤ-in-range
d_fromℤ'45'in'45'range_62 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_62
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_152
      (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_64 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_64 = erased
-- Once.Surface.Elaborate.IntW.fromℤ-neg1
d_fromℤ'45'neg1_66 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_66 = erased
-- Once.Surface.Elaborate.IntW.half
d_half_68 :: Integer
d_half_68
  = coe MAlonzo.Code.Once.Word.d_half_48 (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW.half<modulus
d_half'60'modulus_70 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_70 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_352 (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW.half≡2^b
d_half'8801'2'94'b_72 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_72 = erased
-- Once.Surface.Elaborate.IntW.half≤negOne
d_half'8804'negOne_74 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_74 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_372
      (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW.intMin
d_intMin_76 :: Integer
d_intMin_76
  = coe MAlonzo.Code.Once.Word.d_intMin_54 (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW.modulus
d_modulus_78 :: Integer
d_modulus_78
  = coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_80 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_80 = erased
-- Once.Surface.Elaborate.IntW.modulus≢0
d_modulus'8802'0_82 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_82
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW.mod∸half≡half
d_mod'8760'half'8801'half_84 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_84 = erased
-- Once.Surface.Elaborate.IntW.mod≡half+half
d_mod'8801'half'43'half_86 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_86 = erased
-- Once.Surface.Elaborate.IntW.negOne
d_negOne_88 :: Integer
d_negOne_88
  = coe MAlonzo.Code.Once.Word.d_negOne_56 (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW.negOne<modulus
d_negOne'60'modulus_90 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_90 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_360
      (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW.negOne≢0
d_negOne'8802'0_92 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_92 = erased
-- Once.Surface.Elaborate.IntW.norm
d_norm_94 :: Integer -> Integer
d_norm_94
  = coe MAlonzo.Code.Once.Word.d_norm_16 (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW.norm-0
d_norm'45'0_96 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_96 = erased
-- Once.Surface.Elaborate.IntW.norm-id
d_norm'45'id_98 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_98 = erased
-- Once.Surface.Elaborate.IntW.sdiv2ᵏ
d_sdiv2'7503'_100 :: Integer -> Integer -> Integer
d_sdiv2'7503'_100
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_116 (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW.shlᵂ
d_shl'7490'_102 :: Integer -> Integer -> Integer
d_shl'7490'_102
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_110 (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW.sucNegOne≡mod
d_sucNegOne'8801'mod_104 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_104 = erased
-- Once.Surface.Elaborate.IntW.tdiv-neg1
d_tdiv'45'neg1_106 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_106 = erased
-- Once.Surface.Elaborate.IntW.tmod-neg1
d_tmod'45'neg1_108 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_108 = erased
-- Once.Surface.Elaborate.IntW.toℤ
d_toℤ_110 :: Integer -> Integer
d_toℤ_110
  = coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW.toℤ-negOne
d_toℤ'45'negOne_112 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_112 = erased
-- Once.Surface.Elaborate.IntW.≡ᵇ-refl
d_'8801''7495''45'refl_114 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_114 = erased
-- Once.Surface.Elaborate.IntW.≡ᵇ0-false
d_'8801''7495'0'45'false_116 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_116 = erased
-- Once.Surface.Elaborate.IntW.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_118 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_118 = erased
-- Once.Surface.Elaborate.IntW.⊕-neg
d_'8853''45'neg_120 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_120 = erased
-- Once.Surface.Elaborate.IntW.⊕-neg-suc
d_'8853''45'neg'45'suc_122 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_122 = erased
-- Once.Surface.Elaborate.IntW.⊕-normʳ
d_'8853''45'norm'691'_124 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_124 = erased
-- Once.Surface.Elaborate.IntW.⊕≡+
d_'8853''8801''43'_126 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_126 = erased
-- Once.Surface.Elaborate.IntW.⊖-normʳ
d_'8854''45'norm'691'_128 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_128 = erased
-- Once.Surface.Elaborate.IntW.⊖≡∸
d_'8854''8801''8760'_130 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_130 = erased
-- Once.Surface.Elaborate.IntW.⊗-pow2
d_'8855''45'pow2_132 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_132 = erased
-- Once.Surface.Elaborate.IntW.⊝_
d_'8861'__134 :: Integer -> Integer
d_'8861'__134
  = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
-- Once.Surface.Elaborate.IntW.⊝-intMin
d_'8861''45'intMin_136 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_136 = erased
-- Once.Surface.Elaborate.intLit
d_intLit_140 ::
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
d_intLit_140 v0 ~v1 = du_intLit_140 v0
du_intLit_140 :: Integer -> MAlonzo.Code.Once.IR.T_IR_16
du_intLit_140 v0
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe
         MAlonzo.Code.Once.IR.C_const_148
         (coe MAlonzo.Code.Once.IRTy.C_fits'45'int_512)
         (MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer)) (coe v0)))
      (coe MAlonzo.Code.Once.IR.C_terminal_74)
-- Once.Surface.Elaborate.strLit
d_strLit_146 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
d_strLit_146 v0 ~v1 = du_strLit_146 v0
du_strLit_146 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_strLit_146 v0
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
         (coe MAlonzo.Code.Once.Type.C_Unit_122))
      (coe
         MAlonzo.Code.Once.IR.C_SigOp_154
         (coe MAlonzo.Code.Once.Type.C_Unit_122)
         (coe MAlonzo.Code.Once.Type.C_Str_140)
         (coe
            MAlonzo.Code.Once.Arith.SigOp.Builders.d_str'45'lit'45'info_324
            (coe v0)))
      (coe MAlonzo.Code.Once.IR.C_terminal_74)
-- Once.Surface.Elaborate.floatLit
d_floatLit_152 ::
  MAlonzo.Code.Once.Float.Dyadic.T_Dyadic_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
d_floatLit_152 v0 ~v1 = du_floatLit_152 v0
du_floatLit_152 ::
  MAlonzo.Code.Once.Float.Dyadic.T_Dyadic_6 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_floatLit_152 v0
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe
         MAlonzo.Code.Once.IR.C_const_148
         (coe MAlonzo.Code.Once.IRTy.C_fits'45'float_514) v0)
      (coe MAlonzo.Code.Once.IR.C_terminal_74)
-- Once.Surface.Elaborate.addIR
d_addIR_156 :: MAlonzo.Code.Once.IR.T_IR_16
d_addIR_156
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_154
      (coe
         MAlonzo.Code.Once.Type.C__'42'__126
         (coe MAlonzo.Code.Once.Type.C_Int_136)
         (coe MAlonzo.Code.Once.Type.C_Int_136))
      (coe MAlonzo.Code.Once.Type.C_Int_136)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_300)
-- Once.Surface.Elaborate.subIR
d_subIR_158 :: MAlonzo.Code.Once.IR.T_IR_16
d_subIR_158
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_154
      (coe
         MAlonzo.Code.Once.Type.C__'42'__126
         (coe MAlonzo.Code.Once.Type.C_Int_136)
         (coe MAlonzo.Code.Once.Type.C_Int_136))
      (coe MAlonzo.Code.Once.Type.C_Int_136)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_302)
-- Once.Surface.Elaborate.mulIR
d_mulIR_160 :: MAlonzo.Code.Once.IR.T_IR_16
d_mulIR_160
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_154
      (coe
         MAlonzo.Code.Once.Type.C__'42'__126
         (coe MAlonzo.Code.Once.Type.C_Int_136)
         (coe MAlonzo.Code.Once.Type.C_Int_136))
      (coe MAlonzo.Code.Once.Type.C_Int_136)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_304)
-- Once.Surface.Elaborate.divIR
d_divIR_162 :: MAlonzo.Code.Once.IR.T_IR_16
d_divIR_162
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_154
      (coe
         MAlonzo.Code.Once.Type.C__'42'__126
         (coe MAlonzo.Code.Once.Type.C_Int_136)
         (coe MAlonzo.Code.Once.Type.C_Int_136))
      (coe MAlonzo.Code.Once.Type.C_Int_136)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_306)
-- Once.Surface.Elaborate.modIR
d_modIR_164 :: MAlonzo.Code.Once.IR.T_IR_16
d_modIR_164
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_154
      (coe
         MAlonzo.Code.Once.Type.C__'42'__126
         (coe MAlonzo.Code.Once.Type.C_Int_136)
         (coe MAlonzo.Code.Once.Type.C_Int_136))
      (coe MAlonzo.Code.Once.Type.C_Int_136)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_308)
-- Once.Surface.Elaborate.negIR
d_negIR_166 :: MAlonzo.Code.Once.IR.T_IR_16
d_negIR_166
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_154
      (coe MAlonzo.Code.Once.Type.C_Int_136)
      (coe MAlonzo.Code.Once.Type.C_Int_136)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_neg'45'info_310)
-- Once.Surface.Elaborate.ltIR
d_ltIR_168 :: MAlonzo.Code.Once.IR.T_IR_16
d_ltIR_168
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_154
      (coe
         MAlonzo.Code.Once.Type.C__'42'__126
         (coe MAlonzo.Code.Once.Type.C_Int_136)
         (coe MAlonzo.Code.Once.Type.C_Int_136))
      (coe
         MAlonzo.Code.Once.Type.C__'43'__128
         (coe MAlonzo.Code.Once.Type.C_Unit_122)
         (coe MAlonzo.Code.Once.Type.C_Unit_122))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_312)
-- Once.Surface.Elaborate.leIR
d_leIR_170 :: MAlonzo.Code.Once.IR.T_IR_16
d_leIR_170
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_154
      (coe
         MAlonzo.Code.Once.Type.C__'42'__126
         (coe MAlonzo.Code.Once.Type.C_Int_136)
         (coe MAlonzo.Code.Once.Type.C_Int_136))
      (coe
         MAlonzo.Code.Once.Type.C__'43'__128
         (coe MAlonzo.Code.Once.Type.C_Unit_122)
         (coe MAlonzo.Code.Once.Type.C_Unit_122))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_314)
-- Once.Surface.Elaborate.gtIR
d_gtIR_172 :: MAlonzo.Code.Once.IR.T_IR_16
d_gtIR_172
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_154
      (coe
         MAlonzo.Code.Once.Type.C__'42'__126
         (coe MAlonzo.Code.Once.Type.C_Int_136)
         (coe MAlonzo.Code.Once.Type.C_Int_136))
      (coe
         MAlonzo.Code.Once.Type.C__'43'__128
         (coe MAlonzo.Code.Once.Type.C_Unit_122)
         (coe MAlonzo.Code.Once.Type.C_Unit_122))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_316)
-- Once.Surface.Elaborate.geIR
d_geIR_174 :: MAlonzo.Code.Once.IR.T_IR_16
d_geIR_174
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_154
      (coe
         MAlonzo.Code.Once.Type.C__'42'__126
         (coe MAlonzo.Code.Once.Type.C_Int_136)
         (coe MAlonzo.Code.Once.Type.C_Int_136))
      (coe
         MAlonzo.Code.Once.Type.C__'43'__128
         (coe MAlonzo.Code.Once.Type.C_Unit_122)
         (coe MAlonzo.Code.Once.Type.C_Unit_122))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_318)
-- Once.Surface.Elaborate.eqIR
d_eqIR_176 :: MAlonzo.Code.Once.IR.T_IR_16
d_eqIR_176
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_154
      (coe
         MAlonzo.Code.Once.Type.C__'42'__126
         (coe MAlonzo.Code.Once.Type.C_Int_136)
         (coe MAlonzo.Code.Once.Type.C_Int_136))
      (coe
         MAlonzo.Code.Once.Type.C__'43'__128
         (coe MAlonzo.Code.Once.Type.C_Unit_122)
         (coe MAlonzo.Code.Once.Type.C_Unit_122))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_320)
-- Once.Surface.Elaborate.neIR
d_neIR_178 :: MAlonzo.Code.Once.IR.T_IR_16
d_neIR_178
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_154
      (coe
         MAlonzo.Code.Once.Type.C__'42'__126
         (coe MAlonzo.Code.Once.Type.C_Int_136)
         (coe MAlonzo.Code.Once.Type.C_Int_136))
      (coe
         MAlonzo.Code.Once.Type.C__'43'__128
         (coe MAlonzo.Code.Once.Type.C_Unit_122)
         (coe MAlonzo.Code.Once.Type.C_Unit_122))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_322)
-- Once.Surface.Elaborate.proj
d_proj_186 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> MAlonzo.Code.Once.IR.T_IR_16
d_proj_186 ~v0 v1 v2 = du_proj_186 v1 v2
du_proj_186 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> MAlonzo.Code.Once.IR.T_IR_16
du_proj_186 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Once.IR.C_snd_50
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__30
                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                          (coe v3)))
                    (coe du_proj_186 (coe v3) (coe v7))
                    (coe MAlonzo.Code.Once.IR.C_fst_44)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.swap'
d_swap''_206 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_swap''_206 ~v0 ~v1 v2 = du_swap''_206 v2
du_swap''_206 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
du_swap''_206 v0
  = coe
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
      (coe MAlonzo.Code.Once.IR.C_snd_50)
      (coe MAlonzo.Code.Once.IR.C_fst_44) v0
-- Once.Surface.Elaborate.distribute
d_distribute_216 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_distribute_216 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v1) (coe v2))
         (coe v0))
      (d_distrib''_236 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe du_swap''_206 (coe v3))
-- Once.Surface.Elaborate._.curryInlSwap
d_curryInlSwap_230 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_curryInlSwap_230 v0 v1 ~v2 v3 = du_curryInlSwap_230 v0 v1 v3
du_curryInlSwap_230 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
du_curryInlSwap_230 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_curry_86
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__30
         (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
         (coe MAlonzo.Code.Once.IR.C_inl_56 v2)
         (coe du_swap''_206 (coe v2)))
      v2
-- Once.Surface.Elaborate._.curryInrSwap
d_curryInrSwap_232 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_curryInrSwap_232 v0 ~v1 v2 v3 = du_curryInrSwap_232 v0 v2 v3
du_curryInrSwap_232 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
du_curryInrSwap_232 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_curry_86
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__30
         (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
         (coe MAlonzo.Code.Once.IR.C_inr_62 v2)
         (coe du_swap''_206 (coe v2)))
      v2
-- Once.Surface.Elaborate._.curryDistrib
d_curryDistrib_234 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_curryDistrib_234 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.C_case_70
      (coe du_curryInlSwap_230 (coe v0) (coe v1) (coe v3))
      (coe du_curryInrSwap_232 (coe v0) (coe v2) (coe v3))
-- Once.Surface.Elaborate._.distrib'
d_distrib''_236 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_distrib''_236 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe
            MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0)
            (coe
               MAlonzo.Code.Once.IRTy.C__'43'__22
               (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
               (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v2))))
         (coe v0))
      (coe MAlonzo.Code.Once.IR.C_apply_92)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__30
            (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v1) (coe v2))
            (d_curryDistrib_234 (coe v0) (coe v1) (coe v2) (coe v3))
            (coe MAlonzo.Code.Once.IR.C_fst_44))
         (coe MAlonzo.Code.Once.IR.C_snd_50) v3)
-- Once.Surface.Elaborate.elaborate
d_elaborate_246 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_elaborate_246 ~v0 v1 ~v2 v3 v4 v5 = du_elaborate_246 v1 v3 v4 v5
du_elaborate_246 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_elaborate_246 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_16 v6
        -> coe du_proj_186 (coe v0) (coe v6)
      MAlonzo.Code.Once.Surface.Syntax.C_lam_32 v7 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.IR.C_curry_86
                    (coe
                       du_elaborate_246
                       (coe
                          MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v0 v13
                          (coe MAlonzo.Code.Once.Type.C_Many_10))
                       (coe v15) (coe v2) (coe v12))
                    v2
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_48 v6 v7 v8 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe
                   MAlonzo.Code.Once.IRTy.C__'8667'__24
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v8))
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v1)))
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v8)))
             (coe MAlonzo.Code.Once.IR.C_apply_92)
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_246 (coe v0)
                   (coe
                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v8)
                      (coe
                         MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v10)
                         (coe MAlonzo.Code.Once.Type.C_pure_34))
                      (coe v1))
                   (coe v2) (coe v11))
                (coe du_elaborate_246 (coe v0) (coe v8) (coe v2) (coe v12)) v2)
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_62 v6 v7 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v12 v13 v14
               -> coe
                    MAlonzo.Code.Once.IR.C_curry_86
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__30
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                             (coe v0)))
                       (coe
                          MAlonzo.Code.Once.IR.C__'8728'__30
                          (coe
                             MAlonzo.Code.Once.IRTy.C__'42'__20
                             (coe
                                MAlonzo.Code.Once.IRTy.C__'8667'__24
                                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v8))
                                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v14)))
                             (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v8)))
                          (coe MAlonzo.Code.Once.IR.C_apply_92)
                          (coe
                             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                             (coe
                                du_elaborate_246 (coe v0)
                                (coe
                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v8)
                                   (coe
                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                      (coe MAlonzo.Code.Once.Type.C_eff_36))
                                   (coe v14))
                                (coe v2) (coe v10))
                             (coe du_elaborate_246 (coe v0) (coe v8) (coe v2) (coe v11)) v2))
                       (coe MAlonzo.Code.Once.IR.C_fst_44))
                    v2
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_76 v6 v7 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__126 v12 v13
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                    (coe du_elaborate_246 (coe v0) (coe v12) (coe v2) (coe v10))
                    (coe du_elaborate_246 (coe v0) (coe v13) (coe v2) (coe v11)) v2
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_88 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v1))
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v8)))
             (coe MAlonzo.Code.Once.IR.C_fst_44)
             (coe
                du_elaborate_246 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v1) (coe v8))
                (coe v2) (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_100 v7 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v7))
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v1)))
             (coe MAlonzo.Code.Once.IR.C_snd_50)
             (coe
                du_elaborate_246 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v7) (coe v1))
                (coe v2) (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_112 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__128 v10 v11
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__30
                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v10))
                    (coe MAlonzo.Code.Once.IR.C_inl_56 v2)
                    (coe du_elaborate_246 (coe v0) (coe v10) (coe v2) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_124 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__128 v10 v11
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__30
                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v11))
                    (coe MAlonzo.Code.Once.IR.C_inr_62 v2)
                    (coe du_elaborate_246 (coe v0) (coe v11) (coe v2) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_146 v6 v7 v8 v9 v10 v11 v12 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'43'__22
                (coe
                   MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0)
                         (coe v11))))
                (coe
                   MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0)
                         (coe v12)))))
             (coe
                MAlonzo.Code.Once.IR.C_case_70
                (coe
                   du_elaborate_246
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v11))
                   (coe v1) (coe v2) (coe v15))
                (coe
                   du_elaborate_246
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v12))
                   (coe v1) (coe v2) (coe v16)))
             (coe
                MAlonzo.Code.Once.IR.C__'8728'__30
                (coe
                   MAlonzo.Code.Once.IRTy.C__'42'__20
                   (coe
                      MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe v0)))
                   (coe
                      MAlonzo.Code.Once.IRTy.C__'43'__22
                      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v11))
                      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v12))))
                (d_distribute_216
                   (coe
                      MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe v0)))
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v11))
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v12)) (coe v2))
                (coe
                   MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                   (coe MAlonzo.Code.Once.IR.C_id_22)
                   (coe
                      du_elaborate_246 (coe v0)
                      (coe MAlonzo.Code.Once.Type.C__'43'__128 (coe v11) (coe v12))
                      (coe v2) (coe v14))
                   v2))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_152
        -> coe MAlonzo.Code.Once.IR.C_terminal_74
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_162 v8
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe MAlonzo.Code.Once.IRTy.C_Void_18)
             (coe MAlonzo.Code.Once.IR.C_initial_78)
             (coe
                du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Void_124)
                (coe v2) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_178 v6 v7 v8 v9 v11 v12
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                (coe
                   MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v9))))
             (coe
                du_elaborate_246
                (coe
                   MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v9))
                (coe v1) (coe v2) (coe v12))
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe MAlonzo.Code.Once.IR.C_id_22)
                (coe du_elaborate_246 (coe v0) (coe v9) (coe v2) (coe v11)) v2)
      MAlonzo.Code.Once.Surface.Syntax.C_int_184 v6
        -> coe du_intLit_140 (coe v6)
      MAlonzo.Code.Once.Surface.Syntax.C_str_190 v6
        -> coe du_strLit_146 (coe v6)
      MAlonzo.Code.Once.Surface.Syntax.C_float_198 v6 v7
        -> coe du_floatLit_152 (coe v6)
      MAlonzo.Code.Once.Surface.Syntax.C_add_208 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_addIR_156
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_sub_218 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_subIR_158
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_mul_228 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_mulIR_160
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_div_238 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_divIR_162
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_248 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_modIR_164
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_neg_256 v7
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe MAlonzo.Code.Once.IRTy.C_Int_30) d_negIR_166
             (coe
                du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v2) (coe v7))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_266 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_ltIR_168
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_le_276 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_leIR_170
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_gt_286 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_gtIR_172
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_ge_296 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_geIR_174
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_eq_306 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_eqIR_176
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_ne_316 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_neIR_178
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_246 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_arr''_328 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
               -> coe
                    du_elaborate_246 (coe v0)
                    (coe
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v10)
                       (coe
                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                       (coe v12))
                    (coe v2) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_336 v7 v8
        -> let v9
                 = coe
                     MAlonzo.Code.Once.IR.C__'8728'__30
                     (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                        (coe MAlonzo.Code.Once.Type.C_Unit_122))
                     (coe
                        MAlonzo.Code.Once.IR.C_SigOp_154
                        (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_338
                           (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v1) (coe v7)
                           (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)
                           (coe v8)))
                     (coe MAlonzo.Code.Once.IR.C_terminal_74) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
                  -> case coe v8 of
                       MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v16 v17
                         -> coe
                              MAlonzo.Code.Once.IR.C_curry_86
                              (coe
                                 MAlonzo.Code.Once.IR.C__'8728'__30
                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v10))
                                 (coe
                                    MAlonzo.Code.Once.IR.C_SigOp_154 (coe v10) (coe v12)
                                    (coe
                                       MAlonzo.Code.Once.Arith.SigOp.Builders.d_arrow'45'info_380
                                       (coe v10) (coe v12) (coe v11) (coe v7) (coe v16) (coe v17)))
                                 (coe MAlonzo.Code.Once.IR.C_snd_50))
                              v2
                       _ -> coe v9
                _ -> coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_closure_344 v7
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                (coe MAlonzo.Code.Once.Type.C_Unit_122))
             (coe
                MAlonzo.Code.Once.IR.C_SigOp_154
                (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v1)
                (coe
                   MAlonzo.Code.Once.Arith.SigOp.Builders.d_internal'45'info_348
                   (coe v1) (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v7))))
             (coe MAlonzo.Code.Once.IR.C_terminal_74)
      MAlonzo.Code.Once.Surface.Syntax.C_poly_354 v6
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                (coe MAlonzo.Code.Once.Type.C_Unit_122))
             (coe
                MAlonzo.Code.Once.IR.C_SigOp_154
                (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v1)
                (coe
                   MAlonzo.Code.Once.Arith.SigOp.Builders.d_internal'45'info_348
                   (coe v1) (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v6))))
             (coe MAlonzo.Code.Once.IR.C_terminal_74)
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_366 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
               -> coe
                    MAlonzo.Code.Once.IR.C_curry_86
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__30
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v10)) v9
                       (coe MAlonzo.Code.Once.IR.C_snd_50))
                    v2
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_378 v6 v7 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v7)) v9
             (coe du_elaborate_246 (coe v0) (coe v7) (coe v2) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_cata_390 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v11 v12 v13
               -> case coe v11 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v14
                      -> case coe v12 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                             -> coe
                                  MAlonzo.Code.Once.IR.C_curry_86
                                  (coe
                                     MAlonzo.Code.Once.IR.C__'8728'__30
                                     (coe
                                        MAlonzo.Code.Once.IRTy.C_μ'45'type_26
                                        (coe MAlonzo.Code.Once.IRTy.d_eraseF_40 (coe v14)))
                                     (coe
                                        MAlonzo.Code.Once.IR.C_Cata_106
                                        (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                           (coe v14) (coe v9))
                                        (coe
                                           MAlonzo.Code.Once.IR.C__'8728'__30
                                           (coe
                                              MAlonzo.Code.Once.IRTy.C__'42'__20
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.C__'8667'__24
                                                 (coe
                                                    MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                                    (coe
                                                       MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                       (coe v14) (coe v13)))
                                                 (coe
                                                    MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                                    (coe v13)))
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                                 (coe
                                                    MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                    (coe v14) (coe v13))))
                                           (coe MAlonzo.Code.Once.IR.C_apply_92)
                                           (coe
                                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                                              (coe
                                                 MAlonzo.Code.Once.IR.C__'8728'__30
                                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                                    (coe
                                                       MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                                       (coe
                                                          MAlonzo.Code.Once.Surface.Context.C_'8709'_8)))
                                                 (coe
                                                    du_elaborate_246
                                                    (coe
                                                       MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                       (coe
                                                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                          (coe v14) (coe v13))
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                          (coe v16))
                                                       (coe v13))
                                                    (coe v2) (coe v10))
                                                 (coe MAlonzo.Code.Once.IR.C_terminal_74))
                                              (coe MAlonzo.Code.Once.IR.C_id_22) v2)))
                                     (coe MAlonzo.Code.Once.IR.C_snd_50))
                                  v2
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_402 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v11 v12 v13
               -> case coe v12 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v14 v15
                      -> case coe v13 of
                           MAlonzo.Code.Once.Type.C_ν'45'type_134 v16
                             -> coe
                                  MAlonzo.Code.Once.IR.C_curry_86
                                  (coe
                                     MAlonzo.Code.Once.IR.C__'8728'__30
                                     (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v11))
                                     (coe
                                        MAlonzo.Code.Once.IR.C_Ana_126
                                        (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                           (coe v16) (coe v9))
                                        (coe
                                           MAlonzo.Code.Once.IR.C__'8728'__30
                                           (coe
                                              MAlonzo.Code.Once.IRTy.C__'42'__20
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.C__'8667'__24
                                                 (coe
                                                    MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                                    (coe v11))
                                                 (coe
                                                    MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                                    (coe
                                                       MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                       (coe v16) (coe v11))))
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                                 (coe v11)))
                                           (coe MAlonzo.Code.Once.IR.C_apply_92)
                                           (coe
                                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                                              (coe
                                                 MAlonzo.Code.Once.IR.C__'8728'__30
                                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                                    (coe
                                                       MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                                       (coe
                                                          MAlonzo.Code.Once.Surface.Context.C_'8709'_8)))
                                                 (coe
                                                    du_elaborate_246
                                                    (coe
                                                       MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                       (coe v11)
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                          (coe v15))
                                                       (coe
                                                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                          (coe v16) (coe v11)))
                                                    (coe v2) (coe v10))
                                                 (coe MAlonzo.Code.Once.IR.C_terminal_74))
                                              (coe MAlonzo.Code.Once.IR.C_id_22) v2)))
                                     (coe MAlonzo.Code.Once.IR.C_snd_50))
                                  v2
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.elaborate-default
d_elaborate'45'default_468 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_elaborate'45'default_468 ~v0 v1 ~v2 v3
  = du_elaborate'45'default_468 v1 v3
du_elaborate'45'default_468 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_elaborate'45'default_468 v0 v1
  = coe
      du_elaborate_246 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.IR.C_Heap_8)
-- Once.Surface.Elaborate.distribute-default
d_distribute'45'default_476 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
d_distribute'45'default_476 v0 v1 v2
  = coe
      d_distribute_216 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.IR.C_Heap_8)
