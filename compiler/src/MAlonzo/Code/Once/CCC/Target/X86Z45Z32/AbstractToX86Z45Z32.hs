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
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Target.X86-32.AbstractToX86-32.slot-to-disp
d_slot'45'to'45'disp_10 :: Integer -> Integer
d_slot'45'to'45'disp_10 v0
  = coe
      mulInt (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_68)
-- Once.CCC.Target.X86-32.AbstractToX86-32.compile-abstract
d_compile'45'abstract_14 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26]
d_compile'45'abstract_14 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2082
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edx_16))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2084
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edx_16)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2086
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base_12
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2088
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14)
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_68))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebp_22)
                      (coe d_slot'45'to'45'disp_10 (coe v1)))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebp_22)
                      (coe d_slot'45'to'45'disp_10 (coe v1))))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2094
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base_12
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14)))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2096
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14)
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_68)))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2098 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_lea_30
                (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebp_22)
                   (coe d_slot'45'to'45'disp_10 (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2100 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebp_22)
                      (coe d_slot'45'to'45'disp_10 (coe v1)))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2102 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_sub_38
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_24
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slots_70
                      (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2104 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_add_36
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_24
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slots_70
                      (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2106 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2108 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_push_32
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebp_22)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebp_22))
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_sub_38
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                         (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_24
                         (coe
                            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slots_70
                            (coe v1))))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2110
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebp_22)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_pop_34
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebp_22))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2112
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call_50
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebx_12)
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_68))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2114 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2116 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebp_22)
                      (coe d_slot'45'to'45'disp_10 (coe v1))))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2118 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebp_22)
                      (coe d_slot'45'to'45'disp_10 (coe v1)))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2120 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2126 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call'45'sym_52
                (coe
                   MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_52
                   (coe MAlonzo.Code.Once.SigOp.Info.d_name_174 (coe v3))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2130 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_fits'45'int_198
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_24 (coe v3)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.Type.C_fits'45'float_200
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ud2_58)
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2132 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov'45'code_62
                (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10) (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2134
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebx_12))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2136 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_24 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2138 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ud2_58)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2140 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esi_18)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_add_36
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esi_18))
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_24
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slots_70
                         (coe v1))))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2142 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ud2_58)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2144 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_424
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edx_16))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_24
                          (coe (1 :: Integer))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_426
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edx_16))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_24
                          (coe (0 :: Integer))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_428
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_sub_38
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edx_16))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_24
                          (coe (1 :: Integer))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_430
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edx_16))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edi_20)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_input2'45'zero_432
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edi_20))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_24
                          (coe (0 :: Integer))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_input2'45'inc_434
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_add_36
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edi_20))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_24
                          (coe (1 :: Integer))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2068 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label_60 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2070 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jmp'45'l_64
                       (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2072 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_cmp_40
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                          (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edx_16))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_24
                          (coe (0 :: Integer))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_je_48 (coe v2))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2074 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_cmp_40
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_22
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base_12
                             (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14)))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_24
                          (coe (0 :: Integer))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_je_48 (coe v2))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2148 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                   (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ebp_22)
                      (coe d_slot'45'to'45'disp_10 (coe v1)))))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edx_16)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_add_36
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                         (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                         (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_add_36
                         (coe
                            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                            (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10))
                         (coe
                            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                            (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_add_36
                            (coe
                               MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                               (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14))
                            (coe
                               MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                               (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)))
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.AbstractToX86-32.compile-trace-cnt
d_compile'45'trace'45'cnt_60 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compile'45'trace'45'cnt_60 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      (:) v2 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe d_compile'45'trace'45'cnt_60 (coe v0) (coe v3)))
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe d_compile'45'abstract_14 (coe v2))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                           (coe d_compile'45'trace'45'cnt_60 (coe v0) (coe v3)))) in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2138 v5 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_compile'45'trace'45'cnt_60
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   d_compile'45'trace'45'cnt_60
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         d_compile'45'trace'45'cnt_60
                                         (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v5)))
                                   (coe v6)))
                             (coe v3)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_cmp_40
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base_12
                                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_ecx_14)))
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_24
                                   (coe (0 :: Integer))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_je_48 (coe v0))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_compile'45'trace'45'cnt_60
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               d_compile'45'trace'45'cnt_60
                                               (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v5)))
                                         (coe v6)))
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jmp'45'l_64
                                            (coe addInt (coe (1 :: Integer)) (coe v0)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label_60
                                               (coe v0))
                                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                      (coe
                                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               d_compile'45'trace'45'cnt_60
                                               (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v5)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label_60
                                               (coe addInt (coe (1 :: Integer)) (coe v0)))
                                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_compile'45'trace'45'cnt_60
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_compile'45'trace'45'cnt_60
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            d_compile'45'trace'45'cnt_60
                                            (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v5)))
                                      (coe v6)))
                                (coe v3))))
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2142 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_compile'45'trace'45'cnt_60
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   d_compile'45'trace'45'cnt_60
                                   (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v5)))
                             (coe v3)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label_60 (coe v0))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_cmp_40
                                   (coe
                                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                                      (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edx_16))
                                   (coe
                                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_24
                                      (coe (0 :: Integer))))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_je_48
                                      (coe addInt (coe (1 :: Integer)) (coe v0)))
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            d_compile'45'trace'45'cnt_60
                                            (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v5)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jmp'45'l_64
                                            (coe v0))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label_60
                                               (coe addInt (coe (1 :: Integer)) (coe v0)))
                                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_compile'45'trace'45'cnt_60
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_compile'45'trace'45'cnt_60
                                      (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v5)))
                                (coe v3))))
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.AbstractToX86-32.compile-trace
d_compile'45'trace_120 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26]
d_compile'45'trace_120 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_compile'45'abstract_14 (coe v1))
             (coe d_compile'45'trace_120 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
