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

module MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86 where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.CodeGen.Primitives
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax

-- Once.CCC.Target.X86-64.AbstractToX86.slot-to-disp
d_slot'45'to'45'disp_10 :: Integer -> Integer
d_slot'45'to'45'disp_10 v0
  = coe
      mulInt (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_114)
-- Once.CCC.Target.X86-64.AbstractToX86.compile-abstract
d_compile'45'abstract_14 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_compile'45'abstract_14 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2050
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2052
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2054
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsi_20))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2056
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsi_20)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2058
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_46
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2060
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_114))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2062 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)
                      (coe d_slot'45'to'45'disp_10 (coe v1)))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2064 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)
                      (coe d_slot'45'to'45'disp_10 (coe v1))))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2066
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_46
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2068
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_114)))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2070 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_lea_66
                (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12)
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)
                   (coe d_slot'45'to'45'disp_10 (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2072 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)
                      (coe d_slot'45'to'45'disp_10 (coe v1)))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2074 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_70
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_116
                      (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2076 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_68
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_116
                      (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2078 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2080 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_push_88
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbp_24)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbp_24))
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_70
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                         (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26))
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                         (coe
                            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_116
                            (coe v1))))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2082
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbp_24)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_pop_90
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbp_24))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2084
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call_82
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r12_36)
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_114))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2086 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2088 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)
                      (coe d_slot'45'to'45'disp_10 (coe v1))))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2090 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)
                      (coe d_slot'45'to'45'disp_10 (coe v1)))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2092 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2098 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.CodeGen.Primitives.d_compile'45'sigOp_12
             (coe MAlonzo.Code.Once.CCC.SigOp.Info.d_name_148 (coe v3))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2102 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.CodeGen.Primitives.du_compile'45'const_24
             (coe v2) (coe v3)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2104 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_lea_66
                (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12)
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rip'43'label_52
                   (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2106
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r12_36))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2108 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2110 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_94)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2112 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r15_42)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_68
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r15_42))
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_116
                         (coe v1))))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2114 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_94)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2116 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_424
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                          (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbx_14))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                          (coe (1 :: Integer))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_426
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                          (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbx_14))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                          (coe (0 :: Integer))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_428
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_70
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                          (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbx_14))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                          (coe (1 :: Integer))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_430
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                          (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbx_14))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                          (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsi_20)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_input2'45'zero_432
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                          (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsi_20))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                          (coe (0 :: Integer))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_input2'45'inc_434
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_68
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                          (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsi_20))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                          (coe (1 :: Integer))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2118 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2040 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_98
                       (coe MAlonzo.Code.Once.CCC.Label.C_once_8 (coe v2)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2042 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jmp_76
                       (coe MAlonzo.Code.Once.CCC.Label.C_once_8 (coe v2)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2044 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_cmp_72
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                          (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbx_14))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                          (coe (0 :: Integer))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_je_78
                          (coe MAlonzo.Code.Once.CCC.Label.C_once_8 (coe v2)))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2046 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_cmp_72
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                             (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)
                             (coe (0 :: Integer))))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                          (coe (0 :: Integer))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_je_78
                          (coe MAlonzo.Code.Once.CCC.Label.C_once_8 (coe v2)))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2120 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)
                      (coe d_slot'45'to'45'disp_10 (coe v1)))))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rcx_16))
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbx_14)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_68
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                         (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rcx_16))
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                         (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rcx_16)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_68
                         (coe
                            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rcx_16))
                         (coe
                            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                            (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rcx_16)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_68
                            (coe
                               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rcx_16))
                            (coe
                               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                               (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rcx_16)))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_68
                               (coe
                                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))
                               (coe
                                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                                  (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rcx_16)))
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.AbstractToX86.compile-trace-cnt
d_compile'45'trace'45'cnt_62 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compile'45'trace'45'cnt_62 v0 v1
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
                        (coe d_compile'45'trace'45'cnt_62 (coe v0) (coe v3)))
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe d_compile'45'abstract_14 (coe v2))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                           (coe d_compile'45'trace'45'cnt_62 (coe v0) (coe v3)))) in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2110 v5 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_compile'45'trace'45'cnt_62
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   d_compile'45'trace'45'cnt_62
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         d_compile'45'trace'45'cnt_62
                                         (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v5)))
                                   (coe v6)))
                             (coe v3)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_cmp_72
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_58
                                   (coe
                                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)
                                      (coe (0 :: Integer))))
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                                   (coe (0 :: Integer))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_je_78
                                   (coe MAlonzo.Code.Once.CCC.Label.C_once_8 (coe v0)))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_compile'45'trace'45'cnt_62
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               d_compile'45'trace'45'cnt_62
                                               (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v5)))
                                         (coe v6)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jmp_76
                                         (coe
                                            MAlonzo.Code.Once.CCC.Label.C_once_8
                                            (coe addInt (coe (1 :: Integer)) (coe v0))))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_98
                                            (coe MAlonzo.Code.Once.CCC.Label.C_once_8 (coe v0)))
                                         (coe
                                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_compile'45'trace'45'cnt_62
                                                  (coe addInt (coe (2 :: Integer)) (coe v0))
                                                  (coe v5)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_98
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Label.C_once_8
                                                     (coe addInt (coe (1 :: Integer)) (coe v0))))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_compile'45'trace'45'cnt_62
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_compile'45'trace'45'cnt_62
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            d_compile'45'trace'45'cnt_62
                                            (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v5)))
                                      (coe v6)))
                                (coe v3))))
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2114 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_compile'45'trace'45'cnt_62
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   d_compile'45'trace'45'cnt_62
                                   (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v5)))
                             (coe v3)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_98
                                (coe MAlonzo.Code.Once.CCC.Label.C_once_8 (coe v0)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_cmp_72
                                   (coe
                                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbx_14))
                                   (coe
                                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60
                                      (coe (0 :: Integer))))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_je_78
                                      (coe
                                         MAlonzo.Code.Once.CCC.Label.C_once_8
                                         (coe addInt (coe (1 :: Integer)) (coe v0))))
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            d_compile'45'trace'45'cnt_62
                                            (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v5)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jmp_76
                                            (coe MAlonzo.Code.Once.CCC.Label.C_once_8 (coe v0)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_98
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Label.C_once_8
                                                  (coe addInt (coe (1 :: Integer)) (coe v0))))
                                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_compile'45'trace'45'cnt_62
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_compile'45'trace'45'cnt_62
                                      (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v5)))
                                (coe v3))))
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.AbstractToX86.compile-trace
d_compile'45'trace_122 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_compile'45'trace_122 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_compile'45'abstract_14 (coe v1))
             (coe d_compile'45'trace_122 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
