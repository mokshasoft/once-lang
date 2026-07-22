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

module MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z64 where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Once.Adequacy.CPU.Interface
import qualified MAlonzo.Code.Once.Arith.Backend.RunTraceCore
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Emit
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.RunTrace
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg
import qualified MAlonzo.Code.Once.Word

-- Once.Adequacy.CPU.X86-64.W._%ˢ_
d__'37''738'__10 :: Integer -> Integer -> Integer
d__'37''738'__10
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__104 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W._/ˢ_
d__'47''738'__12 :: Integer -> Integer -> Integer
d__'47''738'__12
  = coe MAlonzo.Code.Once.Word.d__'47''738'__98 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W._<ˢ_
d__'60''738'__14 :: Integer -> Integer -> Bool
d__'60''738'__14
  = coe MAlonzo.Code.Once.Word.d__'60''738'__58 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W._≡ʷ_
d__'8801''695'__16 :: Integer -> Integer -> Bool
d__'8801''695'__16 = coe MAlonzo.Code.Once.Word.du__'8801''695'__64
-- Once.Adequacy.CPU.X86-64.W._⊕_
d__'8853'__18 :: Integer -> Integer -> Integer
d__'8853'__18
  = coe MAlonzo.Code.Once.Word.d__'8853'__26 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W._⊖_
d__'8854'__20 :: Integer -> Integer -> Integer
d__'8854'__20
  = coe MAlonzo.Code.Once.Word.d__'8854'__32 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W._⊗_
d__'8855'__22 :: Integer -> Integer -> Integer
d__'8855'__22
  = coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.%ˢ-else
d_'37''738''45'else_24 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_24 = erased
-- Once.Adequacy.CPU.X86-64.W.%ˢ-in-range
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
-- Once.Adequacy.CPU.X86-64.W.%ˢ-mid
d_'37''738''45'mid_28 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_28 = erased
-- Once.Adequacy.CPU.X86-64.W.%ˢ-negOne
d_'37''738''45'negOne_30 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_30 = erased
-- Once.Adequacy.CPU.X86-64.W.%ˢ-zero
d_'37''738''45'zero_32 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_32 = erased
-- Once.Adequacy.CPU.X86-64.W./ˢ-else
d_'47''738''45'else_34 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_34 = erased
-- Once.Adequacy.CPU.X86-64.W./ˢ-in-range
d_'47''738''45'in'45'range_36 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_36 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_492
      (coe (64 :: Integer)) v2 v3
-- Once.Adequacy.CPU.X86-64.W./ˢ-mid
d_'47''738''45'mid_38 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_38 = erased
-- Once.Adequacy.CPU.X86-64.W./ˢ-negOne
d_'47''738''45'negOne_40 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_40 = erased
-- Once.Adequacy.CPU.X86-64.W./ˢ-pow2
d_'47''738''45'pow2_42 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_42 = erased
-- Once.Adequacy.CPU.X86-64.W./ˢ-zero
d_'47''738''45'zero_44 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_44 = erased
-- Once.Adequacy.CPU.X86-64.W.0<half
d_0'60'half_46 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_46 = coe MAlonzo.Code.Once.Word.du_0'60'half_146
-- Once.Adequacy.CPU.X86-64.W.0<modulus
d_0'60'modulus_48 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_48 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_144
-- Once.Adequacy.CPU.X86-64.W.0<negOne
d_0'60'negOne_50 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_50 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_348 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.2*n≡n+n
d_2'42'n'8801'n'43'n_52 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_52 = erased
-- Once.Adequacy.CPU.X86-64.W.2≤modulus
d_2'8804'modulus_54 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_54 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_344 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.Word
d_Word_56 :: ()
d_Word_56 = erased
-- Once.Adequacy.CPU.X86-64.W.fromℤ
d_fromℤ_58 :: Integer -> Integer
d_fromℤ_58
  = coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.fromℤ-0
d_fromℤ'45'0_60 :: MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_60 = erased
-- Once.Adequacy.CPU.X86-64.W.fromℤ-in-range
d_fromℤ'45'in'45'range_62 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_62
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_152
      (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_64 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_64 = erased
-- Once.Adequacy.CPU.X86-64.W.fromℤ-neg1
d_fromℤ'45'neg1_66 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_66 = erased
-- Once.Adequacy.CPU.X86-64.W.half
d_half_68 :: Integer
d_half_68
  = coe MAlonzo.Code.Once.Word.d_half_48 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.half<modulus
d_half'60'modulus_70 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_70 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_352 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.half≡2^b
d_half'8801'2'94'b_72 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_72 = erased
-- Once.Adequacy.CPU.X86-64.W.half≤negOne
d_half'8804'negOne_74 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_74 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_372
      (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.intMin
d_intMin_76 :: Integer
d_intMin_76
  = coe MAlonzo.Code.Once.Word.d_intMin_54 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.modulus
d_modulus_78 :: Integer
d_modulus_78
  = coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_80 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_80 = erased
-- Once.Adequacy.CPU.X86-64.W.modulus≢0
d_modulus'8802'0_82 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_82
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.mod∸half≡half
d_mod'8760'half'8801'half_84 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_84 = erased
-- Once.Adequacy.CPU.X86-64.W.mod≡half+half
d_mod'8801'half'43'half_86 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_86 = erased
-- Once.Adequacy.CPU.X86-64.W.negOne
d_negOne_88 :: Integer
d_negOne_88
  = coe MAlonzo.Code.Once.Word.d_negOne_56 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.negOne<modulus
d_negOne'60'modulus_90 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_90 v0 v1
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_360
      (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.negOne≢0
d_negOne'8802'0_92 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_92 = erased
-- Once.Adequacy.CPU.X86-64.W.norm
d_norm_94 :: Integer -> Integer
d_norm_94
  = coe MAlonzo.Code.Once.Word.d_norm_16 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.sdiv2ᵏ
d_sdiv2'7503'_96 :: Integer -> Integer -> Integer
d_sdiv2'7503'_96
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_116 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.shlᵂ
d_shl'7490'_98 :: Integer -> Integer -> Integer
d_shl'7490'_98
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_110 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.sucNegOne≡mod
d_sucNegOne'8801'mod_100 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_100 = erased
-- Once.Adequacy.CPU.X86-64.W.tdiv-neg1
d_tdiv'45'neg1_102 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_102 = erased
-- Once.Adequacy.CPU.X86-64.W.tmod-neg1
d_tmod'45'neg1_104 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_104 = erased
-- Once.Adequacy.CPU.X86-64.W.toℤ
d_toℤ_106 :: Integer -> Integer
d_toℤ_106
  = coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.toℤ-negOne
d_toℤ'45'negOne_108 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_108 = erased
-- Once.Adequacy.CPU.X86-64.W.≡ᵇ-refl
d_'8801''7495''45'refl_110 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_110 = erased
-- Once.Adequacy.CPU.X86-64.W.≡ᵇ0-false
d_'8801''7495'0'45'false_112 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_112 = erased
-- Once.Adequacy.CPU.X86-64.W.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_114 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_114 = erased
-- Once.Adequacy.CPU.X86-64.W.⊗-pow2
d_'8855''45'pow2_116 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_116 = erased
-- Once.Adequacy.CPU.X86-64.W.⊝_
d_'8861'__118 :: Integer -> Integer
d_'8861'__118
  = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe (64 :: Integer))
-- Once.Adequacy.CPU.X86-64.W.⊝-intMin
d_'8861''45'intMin_120 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_120 = erased
-- Once.Adequacy.CPU.X86-64.rd
d_rd_122 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 -> Integer
d_rd_122 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Emit.d_arith'45'reg_10
         (coe v1))
-- Once.Adequacy.CPU.X86-64.def
d_def_128 :: Maybe Integer -> Integer
d_def_128 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.X86-64.scratch-addr
d_scratch'45'addr_132 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer
d_scratch'45'addr_132 v0 v1
  = coe
      addInt
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
      (coe
         mulInt (coe (8 :: Integer))
         (coe
            MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.d_slot_20 (coe v1)))
-- Once.Adequacy.CPU.X86-64.side-off
d_side'45'off_138 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22 -> Integer
d_side'45'off_138 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_24
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_26
        -> coe (8 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.X86-64.path-load-go
d_path'45'load'45'go_140 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer
d_path'45'load'45'go_140 v0 v1 v2
  = case coe v2 of
      []
        -> coe
             d_def_128
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readMem_182
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
                   (coe v0))
                (coe v1))
      (:) v3 v4
        -> coe
             d_path'45'load'45'go_140 (coe v0)
             (coe
                d_def_128
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readMem_182
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
                      (coe v0))
                   (coe addInt (coe d_side'45'off_138 (coe v3)) (coe v1))))
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.X86-64.path-load
d_path'45'load_154 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer
d_path'45'load_154 v0 v1
  = coe
      d_path'45'load'45'go_140 (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20))
      (coe v1)
-- Once.Adequacy.CPU.X86-64.val-x86-64
d_val'45'x86'45'64_160 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer
d_val'45'x86'45'64_160 v0 v1 ~v2 = du_val'45'x86'45'64_160 v0 v1
du_val'45'x86'45'64_160 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer
du_val'45'x86'45'64_160 v0 v1
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
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readMem_182
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
                   (coe v1))
                (coe d_scratch'45'addr_132 (coe v1) (coe v3)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'arg_34 v2 v3
        -> coe d_path'45'load_154 (coe v1) (coe v3)
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
-- Once.Adequacy.CPU.X86-64.step-budget-x86-64
d_step'45'budget'45'x86'45'64_266
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-64.step-budget-x86-64"
-- Once.Adequacy.CPU.X86-64.ev-x86-64
d_ev'45'x86'45'64_268
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-64.ev-x86-64"
-- Once.Adequacy.CPU.X86-64.arith-env-x86-64
d_arith'45'env'45'x86'45'64_270
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-64.arith-env-x86-64"
-- Once.Adequacy.CPU.X86-64.run-trace-x86-64
d_run'45'trace'45'x86'45'64_272 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_run'45'trace'45'x86'45'64_272 v0 v1
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'trace_162
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
              (coe v2)))
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
              (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_fetch_554)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_execInstr_332)
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.RunTrace.d_matchCall_10)
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.RunTrace.d_ret'45'past_14)
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v2 v3 v4 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
              (\ v5 v6 v7 -> coe du_val'45'x86'45'64_160 v5 v6) v2 v4))
      (coe d_step'45'budget'45'x86'45'64_266) (coe d_ev'45'x86'45'64_268)
      (coe d_arith'45'env'45'x86'45'64_270 v0) (coe v0) (coe v1)
-- Once.Adequacy.CPU.X86-64.decode-x86-64
d_decode'45'x86'45'64_278
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-64.decode-x86-64"
-- Once.Adequacy.CPU.X86-64.assemble-x86-64
d_assemble'45'x86'45'64_280
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-64.assemble-x86-64"
-- Once.Adequacy.CPU.X86-64.arch-semantics
d_arch'45'semantics_282 ::
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10
d_arch'45'semantics_282
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.Interface.C_constructor_56
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_initState_246
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_run_598
      d_run'45'trace'45'x86'45'64_272 d_decode'45'x86'45'64_278
      d_assemble'45'x86'45'64_280
