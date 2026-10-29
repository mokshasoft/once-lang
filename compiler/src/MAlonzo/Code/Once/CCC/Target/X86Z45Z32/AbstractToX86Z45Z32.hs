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

module MAlonzo.Code.Once.CCC.Target.X86Z45Z32.AbstractToX86Z45Z32 where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Word
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Target.SymbolFresh
import qualified MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW._%ˢ_
d__'37''738'__12 :: Integer -> Integer -> Integer
d__'37''738'__12
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'37''738'__122 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW._/ˢ_
d__'47''738'__14 :: Integer -> Integer -> Integer
d__'47''738'__14
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'47''738'__116 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW._<ˢ_
d__'60''738'__16 :: Integer -> Integer -> Bool
d__'60''738'__16
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'60''738'__76 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW._divℕ_
d__divℕ__18 :: Integer -> Integer -> Integer
d__divℕ__18 = coe MAlonzo.Code.Once.Spec.Word.du__divℕ__88
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW._modℕ_
d__modℕ__20 :: Integer -> Integer -> Integer
d__modℕ__20 = coe MAlonzo.Code.Once.Spec.Word.du__modℕ__90
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW._≡ʷ_
d__'8801''695'__22 :: Integer -> Integer -> Bool
d__'8801''695'__22
  = coe MAlonzo.Code.Once.Spec.Word.du__'8801''695'__82
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW._⊕_
d__'8853'__24 :: Integer -> Integer -> Integer
d__'8853'__24
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8853'__28 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW._⊖_
d__'8854'__26 :: Integer -> Integer -> Integer
d__'8854'__26
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8854'__34 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW._⊗_
d__'8855'__28 :: Integer -> Integer -> Integer
d__'8855'__28
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8855'__40 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW.InRange
d_InRange_30 :: Integer -> ()
d_InRange_30 = erased
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW.Word
d_Word_32 :: ()
d_Word_32 = erased
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW.fromℤ
d_fromℤ_34 :: Integer -> Integer
d_fromℤ_34
  = coe MAlonzo.Code.Once.Spec.Word.d_fromℤ_22 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW.half
d_half_36 :: Integer
d_half_36
  = coe MAlonzo.Code.Once.Spec.Word.d_half_50 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW.inRange?
d_inRange'63'_38 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_38
  = coe
      MAlonzo.Code.Once.Spec.Word.d_inRange'63'_66 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW.intMin
d_intMin_40 :: Integer
d_intMin_40
  = coe MAlonzo.Code.Once.Spec.Word.d_intMin_56 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW.modulus
d_modulus_42 :: Integer
d_modulus_42
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW.modulus≢0
d_modulus'8802'0_44 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_44
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus'8802'0_14
      (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW.negOne
d_negOne_46 :: Integer
d_negOne_46
  = coe MAlonzo.Code.Once.Spec.Word.d_negOne_58 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW.norm
d_norm_48 :: Integer -> Integer
d_norm_48
  = coe MAlonzo.Code.Once.Spec.Word.d_norm_18 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW.tdivℤ
d_tdivℤ_50 :: Integer -> Integer -> Integer
d_tdivℤ_50 = coe MAlonzo.Code.Once.Spec.Word.du_tdivℤ_104
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW.tmodℤ
d_tmodℤ_52 :: Integer -> Integer -> Integer
d_tmodℤ_52 = coe MAlonzo.Code.Once.Spec.Word.du_tmodℤ_106
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW.toWord
d_toWord_54 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_54 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Word.du_toWord_72 (coe (32 :: Integer)) v0
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW.toℤ
d_toℤ_56 :: Integer -> Integer
d_toℤ_56
  = coe MAlonzo.Code.Once.Spec.Word.d_toℤ_52 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW.⊝_
d_'8861'__58 :: Integer -> Integer
d_'8861'__58
  = coe
      MAlonzo.Code.Once.Spec.Word.d_'8861'__46 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.AbstractToX86-32.slot-to-disp
d_slot'45'to'45'disp_60 :: Integer -> Integer
d_slot'45'to'45'disp_60 v0
  = coe
      mulInt (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_78)
-- Once.CCC.Target.X86-32.AbstractToX86-32.compile-abstract
d_compile'45'abstract_64 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28]
d_compile'45'abstract_64 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2256
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2258
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_24
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base_12
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2260
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_24
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14)
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_78))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2262 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_24
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)
                      (coe d_slot'45'to'45'disp_60 (coe v1)))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2264 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_24
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)
                      (coe d_slot'45'to'45'disp_60 (coe v1))))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2266
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_24
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base_12
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14)))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2268
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_24
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14)
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_78)))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2270 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_lea_32
                (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)
                   (coe d_slot'45'to'45'disp_60 (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2272 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_24
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)
                      (coe d_slot'45'to'45'disp_60 (coe v1)))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2274 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_sub_40
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slots_80
                      (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2276 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_add_38
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slots_80
                      (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2278 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2280 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_push_34
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebp_22)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebp_22))
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_sub_40
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                         (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26
                         (coe
                            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slots_80
                            (coe v1))))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2282
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebp_22)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_pop_36
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebp_22))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2284
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call_54
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_24
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebx_12)
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_78))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2286 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2288 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_24
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)
                      (coe d_slot'45'to'45'disp_60 (coe v1))))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2290 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_24
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)
                      (coe d_slot'45'to'45'disp_60 (coe v1)))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2292 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2298 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call'45'sym_56
                (coe
                   MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_58
                   (coe MAlonzo.Code.Once.SigOp.Info.d_name_110 (coe v3))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2304 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_fits'45'int_26
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26
                          (coe
                             MAlonzo.Code.Once.Spec.Word.d_fromℤ_22 (coe (32 :: Integer))
                             (coe v3))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.Type.C_fits'45'float_28
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26
                          (coe
                             MAlonzo.Code.Once.Spec.Float.Decimal.d_round_176
                             (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_binary32_42) (coe v3))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2306 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov'45'code_72
                (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10) (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2308
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebx_12))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2310 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2312 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ud2_64)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2314 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esi_18)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_add_38
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esi_18))
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slots_80
                         (coe v1))))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2316 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ud2_64)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2318 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_366
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edx_16))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26
                          (coe (1 :: Integer))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_368
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edx_16))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26
                          (coe (0 :: Integer))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_370
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_sub_40
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edx_16))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26
                          (coe (1 :: Integer))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_372
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edx_16))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edi_20)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_374
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edi_20))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26
                          (coe (0 :: Integer))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_376
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_add_38
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edi_20))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26
                          (coe (1 :: Integer))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_out'45'nz_378
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_cmp_44
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26
                          (coe (1 :: Integer))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_sbb_42
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                             (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                             (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_add_38
                             (coe
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                                (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                             (coe
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26
                                (coe (1 :: Integer))))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2320 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label_70
                       (coe MAlonzo.Code.Once.CCC.Label.C_once_30 (coe v2)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jmp'45'l_74
                       (coe MAlonzo.Code.Once.CCC.Label.C_once_30 (coe v2)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_cmp_44
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edx_16))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26
                          (coe (0 :: Integer))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_je_52
                          (coe MAlonzo.Code.Once.CCC.Label.C_once_30 (coe v2)))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_cmp_44
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_24
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base_12
                             (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14)))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26
                          (coe (0 :: Integer))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_je_52
                          (coe MAlonzo.Code.Once.CCC.Label.C_once_30 (coe v2)))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236 v2 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label_70
                       (coe MAlonzo.Code.Once.CCC.Label.C_callee_34 (coe v2)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_sub_40
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                             (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26
                             (coe
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slots_80
                                (coe v3))))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2238 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_add_38
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slots_80
                             (coe v2))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ret_60)
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2240 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call'45'l_58
                       (coe
                          MAlonzo.Code.Once.CCC.Label.C_callee_34
                          (coe MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26 (coe v2))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2242 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_sub_40
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slots_80
                             (coe v2))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'leave_2244
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call'45'sym_56
                       (coe
                          MAlonzo.Code.Once.Target.SymbolFresh.d_host'45'leave'45'symbol_164))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2322 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_24
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)
                      (coe d_slot'45'to'45'disp_60 (coe v1)))))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edx_16)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_add_38
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                         (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                         (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_add_38
                         (coe
                            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                            (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                         (coe
                            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                            (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_add_38
                            (coe
                               MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                               (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14))
                            (coe
                               MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                               (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)))
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'free'45'heap_2324 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.AbstractToX86-32.compile-trace-cnt
d_compile'45'trace'45'cnt_124 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compile'45'trace'45'cnt_124 v0 v1 v2
  = case coe v2 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2)
      (:) v3 v4
        -> let v5
                 = coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe d_compile'45'trace'45'cnt_124 (coe v0) (coe v1) (coe v4)))
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe d_compile'45'abstract_64 (coe v3))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                           (coe d_compile'45'trace'45'cnt_124 (coe v0) (coe v1) (coe v4)))) in
           coe
             (case coe v3 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2312 v6 v7
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_compile'45'trace'45'cnt_124 (coe v0)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   d_compile'45'trace'45'cnt_124 (coe v0)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         d_compile'45'trace'45'cnt_124 (coe v0)
                                         (coe addInt (coe (2 :: Integer)) (coe v1)) (coe v6)))
                                   (coe v7)))
                             (coe v4)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_cmp_44
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_24
                                   (coe
                                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base_12
                                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14)))
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26
                                   (coe (0 :: Integer))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_je_52
                                   (coe
                                      MAlonzo.Code.Once.CCC.Label.C_once_30
                                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v1))))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_compile'45'trace'45'cnt_124 (coe v0)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               d_compile'45'trace'45'cnt_124 (coe v0)
                                               (coe addInt (coe (2 :: Integer)) (coe v1)) (coe v6)))
                                         (coe v7)))
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jmp'45'l_74
                                            (coe
                                               MAlonzo.Code.Once.CCC.Label.C_once_30
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                                  (coe addInt (coe (1 :: Integer)) (coe v1)))))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label_70
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Label.C_once_30
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                                     (coe v1))))
                                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                      (coe
                                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               d_compile'45'trace'45'cnt_124 (coe v0)
                                               (coe addInt (coe (2 :: Integer)) (coe v1)) (coe v6)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label_70
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Label.C_once_30
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                                     (coe addInt (coe (1 :: Integer)) (coe v1)))))
                                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_compile'45'trace'45'cnt_124 (coe v0)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_compile'45'trace'45'cnt_124 (coe v0)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            d_compile'45'trace'45'cnt_124 (coe v0)
                                            (coe addInt (coe (2 :: Integer)) (coe v1)) (coe v6)))
                                      (coe v7)))
                                (coe v4))))
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2316 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_compile'45'trace'45'cnt_124 (coe v0)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   d_compile'45'trace'45'cnt_124 (coe v0)
                                   (coe addInt (coe (2 :: Integer)) (coe v1)) (coe v6)))
                             (coe v4)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label_70
                                (coe
                                   MAlonzo.Code.Once.CCC.Label.C_once_30
                                   (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v1))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_cmp_44
                                   (coe
                                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edx_16))
                                   (coe
                                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26
                                      (coe (0 :: Integer))))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_je_52
                                      (coe
                                         MAlonzo.Code.Once.CCC.Label.C_once_30
                                         (coe
                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                            (coe addInt (coe (1 :: Integer)) (coe v1)))))
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            d_compile'45'trace'45'cnt_124 (coe v0)
                                            (coe addInt (coe (2 :: Integer)) (coe v1)) (coe v6)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jmp'45'l_74
                                            (coe
                                               MAlonzo.Code.Once.CCC.Label.C_once_30
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                                  (coe v1))))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label_70
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Label.C_once_30
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                                     (coe addInt (coe (1 :: Integer)) (coe v1)))))
                                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_compile'45'trace'45'cnt_124 (coe v0)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_compile'45'trace'45'cnt_124 (coe v0)
                                      (coe addInt (coe (2 :: Integer)) (coe v1)) (coe v6)))
                                (coe v4))))
                _ -> coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.AbstractToX86-32.compile-trace
d_compile'45'trace_192 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28]
d_compile'45'trace_192 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_compile'45'abstract_64 (coe v1))
             (coe d_compile'45'trace_192 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.AbstractToX86-32.compile-trace-cnt-agrees
d_compile'45'trace'45'cnt'45'agrees_204 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compile'45'trace'45'cnt'45'agrees_204 = erased
