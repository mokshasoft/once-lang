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
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax
import qualified MAlonzo.Code.Once.Float.Word
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Word
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Target.SymbolFresh
import qualified MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW.fromℤ
d_fromℤ_12 :: Integer -> Integer
d_fromℤ_12
  = coe MAlonzo.Code.Once.Spec.Word.d_fromℤ_22 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.AbstractToX86-32.IntW.modulus
d_modulus_14 :: Integer
d_modulus_14
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe (32 :: Integer))
-- Once.CCC.Target.X86-32.AbstractToX86-32.slot-to-disp
d_slot'45'to'45'disp_16 :: Integer -> Integer
d_slot'45'to'45'disp_16 v0
  = coe
      mulInt (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_78)
-- Once.CCC.Target.X86-32.AbstractToX86-32.compile-abstract
d_compile'45'abstract_20 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28]
d_compile'45'abstract_20 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2406
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2408
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2410
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2412
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2414 v1
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
                      (coe d_slot'45'to'45'disp_16 (coe v1)))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2416 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_24
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)
                      (coe d_slot'45'to'45'disp_16 (coe v1))))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2418
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2420
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2422 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_lea_32
                (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)
                   (coe d_slot'45'to'45'disp_16 (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2424 v1
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
                      (coe d_slot'45'to'45'disp_16 (coe v1)))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2426 v1
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2428 v1
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2430 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2432 v1
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2434
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2436
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2438 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2440 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_24
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)
                      (coe d_slot'45'to'45'disp_16 (coe v1))))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2442 v1
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
                      (coe d_slot'45'to'45'disp_16 (coe v1)))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2444 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2450 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call'45'sym_56
                (coe
                   MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_58
                   (coe MAlonzo.Code.Once.SigOp.Info.d_name_116 (coe v3))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2456 v1 v2 v3
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
                             MAlonzo.Code.Once.Float.Word.d_round_58
                             (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_binary32_50) (coe v3))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2458 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov'45'code_72
                (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10) (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2460
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2462 v1
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2464 v1
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2466
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2468 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2380 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label_70
                       (coe MAlonzo.Code.Once.CCC.Label.C_once_30 (coe v2)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2382 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jmp'45'l_74
                       (coe MAlonzo.Code.Once.CCC.Label.C_once_30 (coe v2)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2384 v2
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
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2386 v2 v3
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
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2388 v2
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
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2390 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call'45'l_58
                       (coe
                          MAlonzo.Code.Once.CCC.Label.C_callee_34
                          (coe MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26 (coe v2))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2392 v2
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
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'leave_2394
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call'45'sym_56
                       (coe
                          MAlonzo.Code.Once.Target.SymbolFresh.d_host'45'leave'45'symbol_164))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'free'45'heap_2470 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'room_2472 v1
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
             _ -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_sub_40
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esi_18))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_sub_40
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                             (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esi_18))
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26
                             (coe (1 :: Integer))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_cmp_44
                             (coe
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                                (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esi_18))
                             (coe
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                   (MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe (32 :: Integer)))
                                   (addInt
                                      (coe (1 :: Integer))
                                      (coe
                                         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slots_80
                                         (coe v1))))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jbe'45'fwd_66)
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call'45'sym_56
                                   (coe
                                      MAlonzo.Code.Once.Target.SymbolFresh.d_host'45'exhausted'45'symbol_170))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_local'45'1_68)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_add_38
                                         (coe
                                            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                                            (coe
                                               MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esi_18))
                                         (coe
                                            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_26
                                            (coe (1 :: Integer))))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_add_38
                                            (coe
                                               MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                                               (coe
                                                  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esi_18))
                                            (coe
                                               MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                                               (coe
                                                  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)))
                                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2474 v1
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
                      (coe d_slot'45'to'45'disp_16 (coe v1)))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2476 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_24
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14)
                      (coe d_slot'45'to'45'disp_16 (coe v1))))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_addr'45'at_2478 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_lea_32
                (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14)
                   (coe d_slot'45'to'45'disp_16 (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'rec_2480 v1
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
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_abs'45'sym_18
                      (coe
                         MAlonzo.Code.Once.Target.SymbolFresh.d_alloc'45'record'45'symbol_178)
                      (coe d_slot'45'to'45'disp_16 (coe v1)))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'rec_2482 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_24
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_abs'45'sym_18
                      (coe
                         MAlonzo.Code.Once.Target.SymbolFresh.d_alloc'45'record'45'symbol_178)
                      (coe d_slot'45'to'45'disp_16 (coe v1))))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_22
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.AbstractToX86-32.compile-trace-cnt
d_compile'45'trace'45'cnt_88 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compile'45'trace'45'cnt_88 ~v0 v1 v2
  = du_compile'45'trace'45'cnt_88 v1 v2
du_compile'45'trace'45'cnt_88 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compile'45'trace'45'cnt_88 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      (:) v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe du_compile'45'trace'45'cnt_88 (coe v0) (coe v3)))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_compile'45'abstract_20 (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe du_compile'45'trace'45'cnt_88 (coe v0) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.AbstractToX86-32.compile-trace
d_compile'45'trace_106 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28]
d_compile'45'trace_106 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_compile'45'abstract_20 (coe v1))
             (coe d_compile'45'trace_106 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.AbstractToX86-32.compile-trace-cnt-agrees
d_compile'45'trace'45'cnt'45'agrees_118 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compile'45'trace'45'cnt'45'agrees_118 = erased
