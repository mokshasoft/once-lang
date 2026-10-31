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
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.CodeGen.Primitives
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Target.SymbolFresh
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg

-- Once.CCC.Target.X86-64.AbstractToX86.slot-to-disp
d_slot'45'to'45'disp_10 :: Integer -> Integer
d_slot'45'to'45'disp_10 v0
  = coe
      mulInt (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86)
-- Once.CCC.Target.X86-64.AbstractToX86.compile-abstract
d_compile'45'abstract_14 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30]
d_compile'45'abstract_14 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_32
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_32
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2082
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_32
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_26
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_12
                      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2084
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_32
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_26
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20)
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_32
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_26
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
                      (coe d_slot'45'to'45'disp_10 (coe v1)))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_32
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_26
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
                      (coe d_slot'45'to'45'disp_10 (coe v1))))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2090
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_32
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_26
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_12
                      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20)))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2092
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_32
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_26
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20)
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86)))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2094 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_lea_34
                (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_14
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
                   (coe d_slot'45'to'45'disp_10 (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2096 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_32
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_26
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
                      (coe d_slot'45'to'45'disp_10 (coe v1)))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2098 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_38
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_28
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_88
                      (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2100 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_36
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_28
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_88
                      (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2102 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2104 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_push_60
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbp_22)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_32
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbp_22))
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_38
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_28
                         (coe
                            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_88
                            (coe v1))))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2106
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_32
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbp_22)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_pop_62
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbp_22))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2108
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call_52
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_26
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r12_34)
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2110 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2112 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_32
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_26
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
                      (coe d_slot'45'to'45'disp_10 (coe v1))))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2114 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_32
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_26
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_14
                      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
                      (coe d_slot'45'to'45'disp_10 (coe v1)))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2116 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2122 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.CodeGen.Primitives.d_compile'45'sigOp_62
             (coe MAlonzo.Code.Once.SigOp.Info.d_name_116 (coe v3))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2128 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.CodeGen.Primitives.du_compile'45'const_76
             (coe v2) (coe v3)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2130 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_lea_34
                (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rip'43'label_18
                   (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2132
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_32
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r12_34))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2134 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_32
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_28 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2136 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_32
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r15_40)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_36
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r15_40))
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_28
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_88
                         (coe v1))))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2138
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_cmp_42
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_28
                   (coe (1 :: Integer))))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sbb_40
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10))
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_36
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10))
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_28
                         (coe (1 :: Integer))))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2054 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_70
                       (coe MAlonzo.Code.Once.CCC.Label.C_once_30 (coe v2)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2056 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jmp_46
                       (coe MAlonzo.Code.Once.CCC.Label.C_once_30 (coe v2)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2058 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_cmp_42
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_26
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_14
                             (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20)
                             (coe (0 :: Integer))))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_28
                          (coe (0 :: Integer))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_je_48
                          (coe MAlonzo.Code.Once.CCC.Label.C_once_30 (coe v2)))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2060 v2 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_70
                       (coe MAlonzo.Code.Once.CCC.Label.C_callee_34 (coe v2)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_38
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                             (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_28
                             (coe
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_88
                                (coe v3))))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2062 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_36
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                          (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_28
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_88
                             (coe v2))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ret_58)
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2064 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call'45'l_56
                       (coe
                          MAlonzo.Code.Once.CCC.Label.C_callee_34
                          (coe MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26 (coe v2))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2066 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_lea_34
                       (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r15_40)
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rip'43'sym_20
                          (coe ("once_heap_base" :: Data.Text.Text))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_38
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                             (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_28
                             (coe
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_88
                                (coe v2))))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'leave_2068
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call'45'sym_54
                       (coe
                          MAlonzo.Code.Once.Target.SymbolFresh.d_host'45'leave'45'symbol_164))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.AbstractToX86.compile-trace-cnt
d_compile'45'trace'45'cnt_68 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compile'45'trace'45'cnt_68 ~v0 v1 v2
  = du_compile'45'trace'45'cnt_68 v1 v2
du_compile'45'trace'45'cnt_68 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compile'45'trace'45'cnt_68 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      (:) v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe du_compile'45'trace'45'cnt_68 (coe v0) (coe v3)))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_compile'45'abstract_14 (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe du_compile'45'trace'45'cnt_68 (coe v0) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.AbstractToX86.compile-trace
d_compile'45'trace_86 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30]
d_compile'45'trace_86 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_compile'45'abstract_14 (coe v1))
             (coe d_compile'45'trace_86 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.AbstractToX86.compile-trace-cnt-agrees
d_compile'45'trace'45'cnt'45'agrees_98 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compile'45'trace'45'cnt'45'agrees_98 = erased
