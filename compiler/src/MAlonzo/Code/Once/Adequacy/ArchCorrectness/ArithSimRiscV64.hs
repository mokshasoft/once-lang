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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimRiscV64 where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoad
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion
import qualified MAlonzo.Code.Once.Arith.Backend.RiscV64.Emit
import qualified MAlonzo.Code.Once.Arith.Backend.RiscV64.ExecArith
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.Arith.Machine.AbsState
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics
import qualified MAlonzo.Code.Once.Target.RiscV64.PhysReg
import qualified MAlonzo.Code.Once.Word

-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W._%ˢ_
d__'37''738'__10 :: Integer -> Integer -> Integer
d__'37''738'__10
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__104 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W._/ˢ_
d__'47''738'__12 :: Integer -> Integer -> Integer
d__'47''738'__12
  = coe MAlonzo.Code.Once.Word.d__'47''738'__98 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W._<ˢ_
d__'60''738'__14 :: Integer -> Integer -> Bool
d__'60''738'__14
  = coe MAlonzo.Code.Once.Word.d__'60''738'__58 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W._≡ʷ_
d__'8801''695'__16 :: Integer -> Integer -> Bool
d__'8801''695'__16 = coe MAlonzo.Code.Once.Word.du__'8801''695'__64
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W._⊕_
d__'8853'__18 :: Integer -> Integer -> Integer
d__'8853'__18
  = coe MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W._⊖_
d__'8854'__20 :: Integer -> Integer -> Integer
d__'8854'__20
  = coe MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W._⊗_
d__'8855'__22 :: Integer -> Integer -> Integer
d__'8855'__22
  = coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.%ˢ-else
d_'37''738''45'else_24 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_24 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.%ˢ-in-range
d_'37''738''45'in'45'range_26 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_26 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_526
      (coe (64 :: Integer)) v2 v3 v4
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.%ˢ-mid
d_'37''738''45'mid_28 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_28 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.%ˢ-negOne
d_'37''738''45'negOne_30 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_30 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.%ˢ-zero
d_'37''738''45'zero_32 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_32 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W./ˢ-else
d_'47''738''45'else_34 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_34 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W./ˢ-in-range
d_'47''738''45'in'45'range_36 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_36 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_492
      (coe (64 :: Integer)) v2 v3
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W./ˢ-mid
d_'47''738''45'mid_38 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_38 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W./ˢ-negOne
d_'47''738''45'negOne_40 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_40 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W./ˢ-pow2
d_'47''738''45'pow2_42 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_42 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W./ˢ-zero
d_'47''738''45'zero_44 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_44 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.0<half
d_0'60'half_46 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_46 = coe MAlonzo.Code.Once.Word.du_0'60'half_146
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.0<modulus
d_0'60'modulus_48 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_48 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_144
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.0<negOne
d_0'60'negOne_50 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_50 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_348 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.2*n≡n+n
d_2'42'n'8801'n'43'n_52 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_52 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.2≤modulus
d_2'8804'modulus_54 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_54 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_344 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.Word
d_Word_56 :: ()
d_Word_56 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.fromℤ
d_fromℤ_58 :: Integer -> Integer
d_fromℤ_58
  = coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.fromℤ-0
d_fromℤ'45'0_60 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_60 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.fromℤ-in-range
d_fromℤ'45'in'45'range_62 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_62
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_152
      (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_64 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_64 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.fromℤ-neg1
d_fromℤ'45'neg1_66 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_66 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.half
d_half_68 :: Integer
d_half_68
  = coe MAlonzo.Code.Once.Word.d_half_48 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.half<modulus
d_half'60'modulus_70 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_70 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_352 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.half≡2^b
d_half'8801'2'94'b_72 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_72 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.half≤negOne
d_half'8804'negOne_74 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_74 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_372
      (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.intMin
d_intMin_76 :: Integer
d_intMin_76
  = coe MAlonzo.Code.Once.Word.d_intMin_54 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.modulus
d_modulus_78 :: Integer
d_modulus_78
  = coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_80 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_80 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.modulus≢0
d_modulus'8802'0_82 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_82
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.mod∸half≡half
d_mod'8760'half'8801'half_84 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_84 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.mod≡half+half
d_mod'8801'half'43'half_86 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_86 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.negOne
d_negOne_88 :: Integer
d_negOne_88
  = coe MAlonzo.Code.Once.Word.d_negOne_56 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.negOne<modulus
d_negOne'60'modulus_90 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_90 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_360
      (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.negOne≢0
d_negOne'8802'0_92 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_92 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.norm
d_norm_94 :: Integer -> Integer
d_norm_94
  = coe MAlonzo.Code.Once.Word.d_norm_16 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.sdiv2ᵏ
d_sdiv2'7503'_96 :: Integer -> Integer -> Integer
d_sdiv2'7503'_96
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_116 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.shlᵂ
d_shl'7490'_98 :: Integer -> Integer -> Integer
d_shl'7490'_98
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_110 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.sucNegOne≡mod
d_sucNegOne'8801'mod_100 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_100 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.tdiv-neg1
d_tdiv'45'neg1_102 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_102 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.tmod-neg1
d_tmod'45'neg1_104 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_104 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.toℤ
d_toℤ_106 :: Integer -> Integer
d_toℤ_106
  = coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.toℤ-negOne
d_toℤ'45'negOne_108 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_108 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.≡ᵇ-refl
d_'8801''7495''45'refl_110 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_110 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.≡ᵇ0-false
d_'8801''7495'0'45'false_112 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_112 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_114 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_114 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.⊗-pow2
d_'8855''45'pow2_116 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_116 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.⊝_
d_'8861'__118 :: Integer -> Integer
d_'8861'__118
  = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.W.⊝-intMin
d_'8861''45'intMin_120 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_120 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.rd
d_rd_122 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 -> Integer
d_rd_122 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_readReg_104
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_regs_262 (coe v0))
      (coe
         MAlonzo.Code.Once.Arith.Backend.RiscV64.Emit.d_arith'45'reg_10
         (coe v1))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.def
d_def_128 :: Maybe Integer -> Integer
d_def_128 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.scratch-addr
d_scratch'45'addr_132 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer
d_scratch'45'addr_132 v0 v1
  = coe
      addInt
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_readReg_104
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_regs_262 (coe v0))
         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14))
      (coe
         mulInt (coe (8 :: Integer))
         (coe
            MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.d_slot_20 (coe v1)))
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.side-off
d_side'45'off_138 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22 -> Integer
d_side'45'off_138 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_24
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_26
        -> coe (8 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.path-load-go
d_path'45'load'45'go_142 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer
d_path'45'load'45'go_142
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoad.du_path'45'load'45'go_16
      (coe
         (\ v0 ->
            MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_memory_264
              (coe v0)))
      (coe d_def_128) (coe d_side'45'off_138)
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.plg-mem-cong
d_plg'45'mem'45'cong_144 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_plg'45'mem'45'cong_144 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.HeapChase
d_HeapChase_148 a0 a1 a2 = ()
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.heapchase-agree
d_heapchase'45'agree_150 ::
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.T_HeapChase_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.T_HeapChase_42
d_heapchase'45'agree_150 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.du_heapchase'45'agree_112
      v3 v5
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.plg
d_plg_152 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer
d_plg_152
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.du_plg_26
      (coe d_def_128) (coe d_side'45'off_138)
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.plg-stack-write-invisible
d_plg'45'stack'45'write'45'invisible_154 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.T_HeapChase_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_plg'45'stack'45'write'45'invisible_154 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.pathloadgo≡plg
d_pathloadgo'8801'plg_168 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pathloadgo'8801'plg_168 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.WF
d_WF_182 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 -> ()
d_WF_182 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.path-load
d_path'45'load_190 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer
d_path'45'load_190 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoad.du_path'45'load'45'go_16
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_memory_264
              (coe v2)))
      (coe d_def_128) (coe d_side'45'off_138) (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_readReg_104
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_regs_262 (coe v0))
         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42))
      (coe v1)
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.val-riscv64
d_val'45'riscv64_196 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 -> Integer
d_val'45'riscv64_196 v0 v1 ~v2 = du_val'45'riscv64_196 v0 v1
du_val'45'riscv64_196 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  Integer
du_val'45'riscv64_196 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'imm_26 v2 v3
        -> coe
             MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer)) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_28 v2 v3
        -> coe d_rd_122 (coe v1) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'r'45'm_30 v2 v3
        -> coe d_rd_122 (coe v1) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'm'45'r_32 v2 v3
        -> coe
             d_def_128
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_readMem_236
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_memory_264
                   (coe v1))
                (coe d_scratch'45'addr_132 (coe v1) (coe v3)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'arg_34 v2 v3
        -> coe d_path'45'load_190 (coe v1) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xadd'45'rr_36 v2 v3
        -> coe
             MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer))
             (coe d_rd_122 (coe v1) (coe v2)) (coe d_rd_122 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsub'45'rr_38 v2 v3
        -> coe
             MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
             (coe d_rd_122 (coe v1) (coe v2)) (coe d_rd_122 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Ximul'45'rr_40 v2 v3
        -> coe
             MAlonzo.Code.Once.Word.d__'8855'__38 (coe (64 :: Integer))
             (coe d_rd_122 (coe v1) (coe v2)) (coe d_rd_122 (coe v1) (coe v3))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xneg'45'r_42 v2
        -> coe
             MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
             (coe d_rd_122 (coe v1) (coe v2))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'rrr_44 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'47''738'__98 (coe (64 :: Integer))
             (coe d_rd_122 (coe v1) (coe v3)) (coe d_rd_122 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'rrr_46 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'37''738'__104 (coe (64 :: Integer))
             (coe d_rd_122 (coe v1) (coe v3)) (coe d_rd_122 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'safe'45'rrr_48 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'47''738'__98 (coe (64 :: Integer))
             (coe d_rd_122 (coe v1) (coe v3)) (coe d_rd_122 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'safe'45'rrr_50 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'37''738'__104 (coe (64 :: Integer))
             (coe d_rd_122 (coe v1) (coe v3)) (coe d_rd_122 (coe v1) (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xshl'45'rri_52 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d_shl'7490'_110 (coe (64 :: Integer))
             (coe d_rd_122 (coe v1) (coe v3)) (coe v4)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsdiv'45'pow2'45'rri_54 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d_sdiv2'7503'_116 (coe (64 :: Integer))
             (coe d_rd_122 (coe v1) (coe v3)) (coe v4)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'out_56 v2
        -> coe d_rd_122 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.readReg-wr-arith-other
d_readReg'45'wr'45'arith'45'other_310 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_20 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readReg'45'wr'45'arith'45'other_310 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.readReg-wr-arith-same
d_readReg'45'wr'45'arith'45'same_338 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_20 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readReg'45'wr'45'arith'45'same_338 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.readReg-wr-a0-arith
d_readReg'45'wr'45'a0'45'arith_354 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_20 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readReg'45'wr'45'a0'45'arith_354 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.readReg-wr-a0-same
d_readReg'45'wr'45'a0'45'same_368 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_20 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readReg'45'wr'45'a0'45'same_368 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.rr
d_rr_374 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 -> Integer
d_rr_374 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_readReg_104
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_regs_262 (coe v0))
      (coe v1)
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.mem
d_mem_380 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  Integer -> Maybe Integer
d_mem_380 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_readMem_236
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_memory_264
         (coe v0))
      (coe v1)
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.readMem-writeMem-same
d_readMem'45'writeMem'45'same_392 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readMem'45'writeMem'45'same_392 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.sa-inj
d_sa'45'inj_424 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_sa'45'inj_424 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.wr-arith-t0
d_wr'45'arith'45't0_438 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_20 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wr'45'arith'45't0_438 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64.wr-a0-t0
d_wr'45'a0'45't0_452 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_20 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wr'45'a0'45't0_452 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.sa-inv
d_sa'45'inv_470 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sa'45'inv_470 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.mem-keep
d_mem'45'keep_486 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'keep_486 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.mem-spill-hit
d_mem'45'spill'45'hit_554 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'spill'45'hit_554 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.mem-spill-miss
d_mem'45'spill'45'miss_570 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'spill'45'miss_570 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.V
d_V_582 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  Integer
d_V_582 ~v0 v1 v2 = du_V_582 v1 v2
du_V_582 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  Integer
du_V_582 v0 v1 = coe du_val'45'riscv64_196 (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.rf-other
d_rf'45'other_596 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rf'45'other_596 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.t0-inv
d_t0'45'inv_770 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_t0'45'inv_770 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.pl-inv-ns
d_pl'45'inv'45'ns_882 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pl'45'inv'45'ns_882 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.mem-agree-heap
d_mem'45'agree'45'heap_902 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'agree'45'heap_902 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.wf-e1
d_wf'45'e1_1108 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'e1_1108 ~v0 ~v1 ~v2 v3 = du_wf'45'e1_1108 v3
du_wf'45'e1_1108 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf'45'e1_1108 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe (\ v3 -> coe v1 v3))
             (coe
                (\ v3 ->
                   coe
                     MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.du_heapchase'45'agree_112
                     (coe v3) (coe v2 v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._.pl-inv
d_pl'45'inv_1130 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pl'45'inv_1130 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.R
d_R_1412 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 -> ()
d_R_1412 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.R-init
d_R'45'init_1414 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'init_1414 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.R-input
d_R'45'input_1416 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 -> ()
d_R'45'input_1416 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.R-scratch
d_R'45'scratch_1418 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 -> ()
d_R'45'scratch_1418 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.R-scratch-init
d_R'45'scratch'45'init_1420 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'scratch'45'init_1420 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.R-step-arg
d_R'45'step'45'arg_1422 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'step'45'arg_1422 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.R-step-full
d_R'45'step'45'full_1424 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'step'45'full_1424 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.R-step-reload
d_R'45'step'45'reload_1426 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'step'45'reload_1426 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.Rf
d_Rf_1428 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 -> ()
d_Rf_1428 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.Rf-init
d_Rf'45'init_1430 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'init_1430 ~v0 = du_Rf'45'init_1430
du_Rf'45'init_1430 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_Rf'45'init_1430 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore.du_Rf'45'init_2104
      v3 v4
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.Rf-sim
d_Rf'45'sim_1432 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'sim_1432 ~v0 = du_Rf'45'sim_1432
du_Rf'45'sim_1432 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_Rf'45'sim_1432 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore.du_Rf'45'sim_2054
      (coe
         MAlonzo.Code.Once.Arith.Backend.RiscV64.ExecArith.du_exec1_68
         (\ v5 v6 v7 -> coe du_val'45'riscv64_196 v5 v6))
      (\ v5 v6 v7 -> coe du_wf'45'e1_1108 v7) v1 v3 v4
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.Rf-step
d_Rf'45'step_1434 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'step_1434 ~v0 = du_Rf'45'step_1434
du_Rf'45'step_1434 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_Rf'45'step_1434 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore.du_Rf'45'step_2028
      (\ v5 v6 v7 -> coe du_wf'45'e1_1108 v7) v1 v3 v4
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.arith-block-correct
d_arith'45'block'45'correct_1436 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arith'45'block'45'correct_1436 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.bin-value
d_bin'45'value_1438 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  Integer ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bin'45'value_1438 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.eb-++
d_eb'45''43''43'_1440 ::
  Integer ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eb'45''43''43'_1440 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.frame-hyp
d_frame'45'hyp_1442 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_frame'45'hyp_1442 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.input-frame
d_input'45'frame_1444 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45'frame_1444 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.no-tgt-hyp
d_no'45'tgt'45'hyp_1446 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'tgt'45'hyp_1446 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.nonspill-sf
d_nonspill'45'sf_1448 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nonspill'45'sf_1448 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.n≢j
d_n'8802'j_1450 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8802'j_1450 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.output-extract
d_output'45'extract_1452 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_output'45'extract_1452 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.result-correct
d_result'45'correct_1454 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  Integer ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result'45'correct_1454 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.sa-slot-eq
d_sa'45'slot'45'eq_1456 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sa'45'slot'45'eq_1456 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.scratch-frame
d_scratch'45'frame_1458 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45'frame_1458 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.step-other
d_step'45'other_1460 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Maybe Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'other_1460 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.un-value
d_un'45'value_1462 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  Integer ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_un'45'value_1462 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64._._.xreg-idx-inj
d_xreg'45'idx'45'inj_1464 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xreg'45'idx'45'inj_1464 = erased
