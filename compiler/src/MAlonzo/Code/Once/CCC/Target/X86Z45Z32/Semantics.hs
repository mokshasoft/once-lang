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

module MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax

-- Once.CCC.Target.X86-32.Semantics.Word
d_Word_10 :: ()
d_Word_10 = erased
-- Once.CCC.Target.X86-32.Semantics.RegFile
d_RegFile_12 = ()
data T_RegFile_12
  = C_mkregfile_46 Integer Integer Integer Integer Integer Integer
                   Integer Integer
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-eax
d_get'45'eax_30 :: T_RegFile_12 -> Integer
d_get'45'eax_30 v0
  = case coe v0 of
      C_mkregfile_46 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-ebx
d_get'45'ebx_32 :: T_RegFile_12 -> Integer
d_get'45'ebx_32 v0
  = case coe v0 of
      C_mkregfile_46 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-ecx
d_get'45'ecx_34 :: T_RegFile_12 -> Integer
d_get'45'ecx_34 v0
  = case coe v0 of
      C_mkregfile_46 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-edx
d_get'45'edx_36 :: T_RegFile_12 -> Integer
d_get'45'edx_36 v0
  = case coe v0 of
      C_mkregfile_46 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-esi
d_get'45'esi_38 :: T_RegFile_12 -> Integer
d_get'45'esi_38 v0
  = case coe v0 of
      C_mkregfile_46 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-edi
d_get'45'edi_40 :: T_RegFile_12 -> Integer
d_get'45'edi_40 v0
  = case coe v0 of
      C_mkregfile_46 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-ebp
d_get'45'ebp_42 :: T_RegFile_12 -> Integer
d_get'45'ebp_42 v0
  = case coe v0 of
      C_mkregfile_46 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.RegFile.get-esp
d_get'45'esp_44 :: T_RegFile_12 -> Integer
d_get'45'esp_44 v0
  = case coe v0 of
      C_mkregfile_46 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.readReg
d_readReg_48 ::
  T_RegFile_12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Reg_10 -> Integer
d_readReg_48 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_eax_12
        -> coe d_get'45'eax_30 (coe v0)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ebx_14
        -> coe d_get'45'ebx_32 (coe v0)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ecx_16
        -> coe d_get'45'ecx_34 (coe v0)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_edx_18
        -> coe d_get'45'edx_36 (coe v0)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_esi_20
        -> coe d_get'45'esi_38 (coe v0)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_edi_22
        -> coe d_get'45'edi_40 (coe v0)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ebp_24
        -> coe d_get'45'ebp_42 (coe v0)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_esp_26
        -> coe d_get'45'esp_44 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.writeReg
d_writeReg_66 ::
  T_RegFile_12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Reg_10 ->
  Integer -> T_RegFile_12
d_writeReg_66 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_eax_12
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_46 (coe v2) (coe d_get'45'ebx_32 (coe v0))
                  (coe d_get'45'ecx_34 (coe v0)) (coe d_get'45'edx_36 (coe v0))
                  (coe d_get'45'esi_38 (coe v0)) (coe d_get'45'edi_40 (coe v0))
                  (coe d_get'45'ebp_42 (coe v0)) (coe d_get'45'esp_44 (coe v0)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ebx_14
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_46 (coe d_get'45'eax_30 (coe v0)) (coe v2)
                  (coe d_get'45'ecx_34 (coe v0)) (coe d_get'45'edx_36 (coe v0))
                  (coe d_get'45'esi_38 (coe v0)) (coe d_get'45'edi_40 (coe v0))
                  (coe d_get'45'ebp_42 (coe v0)) (coe d_get'45'esp_44 (coe v0)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ecx_16
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_46 (coe d_get'45'eax_30 (coe v0))
                  (coe d_get'45'ebx_32 (coe v0)) (coe v2)
                  (coe d_get'45'edx_36 (coe v0)) (coe d_get'45'esi_38 (coe v0))
                  (coe d_get'45'edi_40 (coe v0)) (coe d_get'45'ebp_42 (coe v0))
                  (coe d_get'45'esp_44 (coe v0)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_edx_18
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_46 (coe d_get'45'eax_30 (coe v0))
                  (coe d_get'45'ebx_32 (coe v0)) (coe d_get'45'ecx_34 (coe v0))
                  (coe v2) (coe d_get'45'esi_38 (coe v0))
                  (coe d_get'45'edi_40 (coe v0)) (coe d_get'45'ebp_42 (coe v0))
                  (coe d_get'45'esp_44 (coe v0)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_esi_20
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_46 (coe d_get'45'eax_30 (coe v0))
                  (coe d_get'45'ebx_32 (coe v0)) (coe d_get'45'ecx_34 (coe v0))
                  (coe d_get'45'edx_36 (coe v0)) (coe v2)
                  (coe d_get'45'edi_40 (coe v0)) (coe d_get'45'ebp_42 (coe v0))
                  (coe d_get'45'esp_44 (coe v0)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_edi_22
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_46 (coe d_get'45'eax_30 (coe v0))
                  (coe d_get'45'ebx_32 (coe v0)) (coe d_get'45'ecx_34 (coe v0))
                  (coe d_get'45'edx_36 (coe v0)) (coe d_get'45'esi_38 (coe v0))
                  (coe v2) (coe d_get'45'ebp_42 (coe v0))
                  (coe d_get'45'esp_44 (coe v0)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ebp_24
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_46 (coe d_get'45'eax_30 (coe v0))
                  (coe d_get'45'ebx_32 (coe v0)) (coe d_get'45'ecx_34 (coe v0))
                  (coe d_get'45'edx_36 (coe v0)) (coe d_get'45'esi_38 (coe v0))
                  (coe d_get'45'edi_40 (coe v0)) (coe v2)
                  (coe d_get'45'esp_44 (coe v0)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_esp_26
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_46 (coe d_get'45'eax_30 (coe v0))
                  (coe d_get'45'ebx_32 (coe v0)) (coe d_get'45'ecx_34 (coe v0))
                  (coe d_get'45'edx_36 (coe v0)) (coe d_get'45'esi_38 (coe v0))
                  (coe d_get'45'edi_40 (coe v0)) (coe d_get'45'ebp_42 (coe v0))
                  (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.Memory
d_Memory_100 :: ()
d_Memory_100 = erased
-- Once.CCC.Target.X86-32.Semantics.readMem
d_readMem_102 ::
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
d_readMem_102 v0 v1 = coe v0 v1
-- Once.CCC.Target.X86-32.Semantics.writeMem
d_writeMem_108 ::
  (Integer -> Maybe Integer) ->
  Integer -> Integer -> Integer -> Maybe Integer
d_writeMem_108 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v3) (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
      (coe v0 v3)
-- Once.CCC.Target.X86-32.Semantics.Flags
d_Flags_118 = ()
data T_Flags_118 = C_mkflags_132 Bool Bool Bool
-- Once.CCC.Target.X86-32.Semantics.Flags.zf
d_zf_126 :: T_Flags_118 -> Bool
d_zf_126 v0
  = case coe v0 of
      C_mkflags_132 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.Flags.cf
d_cf_128 :: T_Flags_118 -> Bool
d_cf_128 v0
  = case coe v0 of
      C_mkflags_132 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.Flags.sf
d_sf_130 :: T_Flags_118 -> Bool
d_sf_130 v0
  = case coe v0 of
      C_mkflags_132 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.State
d_State_134 = ()
data T_State_134
  = C_mkstate_156 T_RegFile_12 (Integer -> Maybe Integer) T_Flags_118
                  Integer Bool
-- Once.CCC.Target.X86-32.Semantics.State.regs
d_regs_146 :: T_State_134 -> T_RegFile_12
d_regs_146 v0
  = case coe v0 of
      C_mkstate_156 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.State.memory
d_memory_148 :: T_State_134 -> Integer -> Maybe Integer
d_memory_148 v0
  = case coe v0 of
      C_mkstate_156 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.State.flags
d_flags_150 :: T_State_134 -> T_Flags_118
d_flags_150 v0
  = case coe v0 of
      C_mkstate_156 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.State.pc
d_pc_152 :: T_State_134 -> Integer
d_pc_152 v0
  = case coe v0 of
      C_mkstate_156 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.State.halted
d_halted_154 :: T_State_134 -> Bool
d_halted_154 v0
  = case coe v0 of
      C_mkstate_156 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.emptyRegFile
d_emptyRegFile_158 :: T_RegFile_12
d_emptyRegFile_158
  = coe
      C_mkregfile_46 (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.CCC.Target.X86-32.Semantics.emptyMemory
d_emptyMemory_160 :: Integer -> Maybe Integer
d_emptyMemory_160 ~v0 = du_emptyMemory_160
du_emptyMemory_160 :: Maybe Integer
du_emptyMemory_160
  = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.CCC.Target.X86-32.Semantics.initFlags
d_initFlags_164 :: T_Flags_118
d_initFlags_164
  = coe
      C_mkflags_132 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.CCC.Target.X86-32.Semantics.initState
d_initState_166 :: T_State_134
d_initState_166
  = coe
      C_mkstate_156 (coe d_emptyRegFile_158)
      (\ v0 -> coe du_emptyMemory_160) (coe d_initFlags_164)
      (coe (0 :: Integer)) (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.CCC.Target.X86-32.Semantics.effectiveAddr
d_effectiveAddr_168 ::
  T_State_134 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Mem_28 -> Integer
d_effectiveAddr_168 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base_30 v2
        -> coe d_readReg_48 (coe d_regs_146 (coe v0)) (coe v2)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_32 v2 v3
        -> coe
             addInt (coe d_readReg_48 (coe d_regs_146 (coe v0)) (coe v2))
             (coe v3)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label'45'rel_34 v2
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.readOperand
d_readOperand_184 ::
  T_State_134 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Operand_36 ->
  Maybe Integer
d_readOperand_184 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_38 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe d_readReg_48 (coe d_regs_146 (coe v0)) (coe v2))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_40 v2
        -> coe
             d_readMem_102 (coe d_memory_148 (coe v0))
             (coe d_effectiveAddr_168 (coe v0) (coe v2))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_42 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.writeOperand
d_writeOperand_198 ::
  T_State_134 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Operand_36 ->
  Integer -> T_State_134
d_writeOperand_198 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_38 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkstate_156 (coe d_writeReg_66 (d_regs_146 (coe v0)) v2 v3)
                  (coe d_memory_148 (coe v0)) (coe d_flags_150 (coe v0))
                  (coe d_pc_152 (coe v0)) (coe d_halted_154 (coe v0)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_40 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkstate_156 (coe d_regs_146 (coe v0))
                  (coe
                     d_writeMem_108 (coe d_memory_148 (coe v0))
                     (coe d_effectiveAddr_168 (coe v0) (coe v2)) (coe v3))
                  (coe d_flags_150 (coe v0)) (coe d_pc_152 (coe v0))
                  (coe d_halted_154 (coe v0)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_42 v2
        -> coe (\ v3 -> v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.updateFlags
d_updateFlags_214 :: Integer -> T_Flags_118
d_updateFlags_214 v0
  = coe
      C_mkflags_132 (coe eqInt (coe v0) (coe (0 :: Integer)))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.CCC.Target.X86-32.Semantics._<ᵇ_
d__'60''7495'__218 :: Integer -> Integer -> Bool
d__'60''7495'__218 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe (coe d__'60''7495'__218 (coe v2) (coe v3)))
-- Once.CCC.Target.X86-32.Semantics.execInstr
d_execInstr_224 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_44] ->
  T_State_134 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_44 ->
  Maybe T_State_134
d_execInstr_224 ~v0 v1 v2 = du_execInstr_224 v1 v2
du_execInstr_224 ::
  T_State_134 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_44 ->
  Maybe T_State_134
du_execInstr_224 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_46 v2 v3
        -> let v4 = d_readOperand_184 (coe v0) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_156 (coe d_regs_146 (coe d_writeOperand_198 v0 v2 v5))
                          (coe d_memory_148 (coe d_writeOperand_198 v0 v2 v5))
                          (coe d_flags_150 (coe d_writeOperand_198 v0 v2 v5))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_152 (coe v0)))
                          (coe d_halted_154 (coe d_writeOperand_198 v0 v2 v5)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_lea_48 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_156
                (coe
                   d_writeReg_66 (d_regs_146 (coe v0)) v2
                   (d_effectiveAddr_168 (coe v0) (coe v3)))
                (coe d_memory_148 (coe v0)) (coe d_flags_150 (coe v0))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_152 (coe v0)))
                (coe d_halted_154 (coe v0)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_push_50 v2
        -> let v3 = d_readOperand_184 (coe v0) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_156
                          (coe
                             d_writeReg_66 (d_regs_146 (coe v0))
                             (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_esp_26)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_48
                                   (coe d_regs_146 (coe v0))
                                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_esp_26))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_82))
                          (coe
                             d_writeMem_108 (coe d_memory_148 (coe v0))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_48
                                   (coe d_regs_146 (coe v0))
                                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_esp_26))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_82)
                             (coe v4))
                          (coe d_flags_150 (coe v0))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_152 (coe v0)))
                          (coe d_halted_154 (coe v0)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_pop_52 v2
        -> let v3
                 = d_readMem_102
                     (coe d_memory_148 (coe v0))
                     (coe
                        d_readReg_48 (coe d_regs_146 (coe v0))
                        (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_esp_26)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_156
                          (coe
                             d_writeReg_66 (coe d_writeReg_66 (d_regs_146 (coe v0)) v2 v4)
                             (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_esp_26)
                             (addInt
                                (coe
                                   d_readReg_48 (coe d_regs_146 (coe v0))
                                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_esp_26))
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_82)))
                          (coe d_memory_148 (coe v0)) (coe d_flags_150 (coe v0))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_152 (coe v0)))
                          (coe d_halted_154 (coe v0)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_add_54 v2 v3
        -> let v4 = d_readOperand_184 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> let v6 = d_readOperand_184 (coe v0) (coe v3) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_156
                                    (coe
                                       d_regs_146
                                       (coe d_writeOperand_198 v0 v2 (addInt (coe v5) (coe v7))))
                                    (coe
                                       d_memory_148
                                       (coe d_writeOperand_198 v0 v2 (addInt (coe v5) (coe v7))))
                                    (coe d_updateFlags_214 (coe addInt (coe v5) (coe v7)))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_152 (coe v0)))
                                    (coe
                                       d_halted_154
                                       (coe d_writeOperand_198 v0 v2 (addInt (coe v5) (coe v7)))))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_sub_56 v2 v3
        -> let v4 = d_readOperand_184 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> let v6 = d_readOperand_184 (coe v0) (coe v3) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_156
                                    (coe
                                       d_regs_146
                                       (coe
                                          d_writeOperand_198 v0 v2
                                          (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v5 v7)))
                                    (coe
                                       d_memory_148
                                       (coe
                                          d_writeOperand_198 v0 v2
                                          (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v5 v7)))
                                    (coe
                                       d_updateFlags_214
                                       (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v5 v7))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_152 (coe v0)))
                                    (coe
                                       d_halted_154
                                       (coe
                                          d_writeOperand_198 v0 v2
                                          (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v5 v7))))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_cmp_58 v2 v3
        -> let v4 = d_readOperand_184 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> let v6 = d_readOperand_184 (coe v0) (coe v3) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_156 (coe d_regs_146 (coe v0))
                                    (coe d_memory_148 (coe v0))
                                    (coe
                                       C_mkflags_132 (coe eqInt (coe v5) (coe v7))
                                       (coe d__'60''7495'__218 (coe v5) (coe v7))
                                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_152 (coe v0)))
                                    (coe d_halted_154 (coe v0)))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_test_60 v2 v3
        -> let v4 = d_readOperand_184 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> let v6 = d_readOperand_184 (coe v0) (coe v3) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_156 (coe d_regs_146 (coe v0))
                                    (coe d_memory_148 (coe v0))
                                    (coe
                                       C_mkflags_132 (coe eqInt (coe v5) (coe (0 :: Integer)))
                                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_152 (coe v0)))
                                    (coe d_halted_154 (coe v0)))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jmp_62 v2
        -> let v3 = d_readOperand_184 (coe v0) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_156 (coe d_regs_146 (coe v0)) (coe d_memory_148 (coe v0))
                          (coe d_flags_150 (coe v0)) (coe v4) (coe d_halted_154 (coe v0)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jne_64 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_156 (coe d_regs_146 (coe v0)) (coe d_memory_148 (coe v0))
                (coe d_flags_150 (coe v0))
                (coe
                   MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                   (coe d_zf_126 (coe d_flags_150 (coe v0)))
                   (coe addInt (coe (1 :: Integer)) (coe d_pc_152 (coe v0)))
                   (coe
                      addInt (coe addInt (coe (1 :: Integer)) (coe d_pc_152 (coe v0)))
                      (coe v2)))
                (coe d_halted_154 (coe v0)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_je_66 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_156 (coe d_regs_146 (coe v0)) (coe d_memory_148 (coe v0))
                (coe d_flags_150 (coe v0))
                (coe
                   MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                   (coe d_zf_126 (coe d_flags_150 (coe v0)))
                   (coe
                      addInt (coe addInt (coe (1 :: Integer)) (coe d_pc_152 (coe v0)))
                      (coe v2))
                   (coe addInt (coe (1 :: Integer)) (coe d_pc_152 (coe v0))))
                (coe d_halted_154 (coe v0)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call_68 v2
        -> let v3 = d_readOperand_184 (coe v0) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_156
                          (coe
                             d_writeReg_66 (d_regs_146 (coe v0))
                             (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_esp_26)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_48
                                   (coe d_regs_146 (coe v0))
                                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_esp_26))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_82))
                          (coe
                             d_writeMem_108 (coe d_memory_148 (coe v0))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_48
                                   (coe d_regs_146 (coe v0))
                                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_esp_26))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_82)
                             (coe addInt (coe (1 :: Integer)) (coe d_pc_152 (coe v0))))
                          (coe d_flags_150 (coe v0)) (coe v4) (coe d_halted_154 (coe v0)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call'45'sym_70 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_156 (coe d_regs_146 (coe v0)) (coe d_memory_148 (coe v0))
                (coe d_flags_150 (coe v0)) (coe d_pc_152 (coe v0))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ret_72
        -> let v2
                 = d_readMem_102
                     (coe d_memory_148 (coe v0))
                     (coe
                        d_readReg_48 (coe d_regs_146 (coe v0))
                        (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_esp_26)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_156
                          (coe
                             d_writeReg_66 (d_regs_146 (coe v0))
                             (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_esp_26)
                             (addInt
                                (coe
                                   d_readReg_48 (coe d_regs_146 (coe v0))
                                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_esp_26))
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_82)))
                          (coe d_memory_148 (coe v0)) (coe d_flags_150 (coe v0)) (coe v3)
                          (coe d_halted_154 (coe v0)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_nop_74
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_156 (coe d_regs_146 (coe v0)) (coe d_memory_148 (coe v0))
                (coe d_flags_150 (coe v0))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_152 (coe v0)))
                (coe d_halted_154 (coe v0)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ud2_76
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_156 (coe d_regs_146 (coe v0)) (coe d_memory_148 (coe v0))
                (coe d_flags_150 (coe v0)) (coe d_pc_152 (coe v0))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label_78 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_156 (coe d_regs_146 (coe v0)) (coe d_memory_148 (coe v0))
                (coe d_flags_150 (coe v0))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_152 (coe v0)))
                (coe d_halted_154 (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.fetch
d_fetch_402 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_44] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_44
d_fetch_402 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe d_fetch_402 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Semantics.step-not-halted
d_step'45'not'45'halted_410 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_44] ->
  T_State_134 -> Maybe T_State_134
d_step'45'not'45'halted_410 v0 v1
  = let v2 = d_fetch_402 (coe v0) (coe d_pc_152 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe du_execInstr_224 (coe v1) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   C_mkstate_156 (coe d_regs_146 (coe v1)) (coe d_memory_148 (coe v1))
                   (coe d_flags_150 (coe v1)) (coe d_pc_152 (coe v1))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Target.X86-32.Semantics.step
d_step_420 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_44] ->
  T_State_134 -> Maybe T_State_134
d_step_420 v0 v1
  = let v2 = d_halted_154 (coe v1) in
    coe
      (if coe v2
         then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
         else coe d_step'45'not'45'halted_410 (coe v0) (coe v1))
-- Once.CCC.Target.X86-32.Semantics.exec
d_exec_438 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_44] ->
  T_State_134 -> Maybe T_State_134
d_exec_438 v0 v1 v2
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (let v4 = d_halted_154 (coe v2) in
              coe
                (if coe v4
                   then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                   else (let v5 = d_step'45'not'45'halted_410 (coe v1) (coe v2) in
                         coe
                           (case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                -> let v7 = d_halted_154 (coe v6) in
                                   coe
                                     (if coe v7
                                        then coe v5
                                        else coe d_exec_438 (coe v3) (coe v1) (coe v6))
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Target.X86-32.Semantics.defaultFuel
d_defaultFuel_502 :: Integer
d_defaultFuel_502 = coe (10000 :: Integer)
-- Once.CCC.Target.X86-32.Semantics.run
d_run_504 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_44] ->
  T_State_134 -> Maybe T_State_134
d_run_504 = coe d_exec_438 (coe d_defaultFuel_502)
