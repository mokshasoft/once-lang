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
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.CodeGen.Compile
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax

-- Once.CCC.Target.X86-64.AbstractToX86.slot-to-disp
d_slot'45'to'45'disp_10 :: Integer -> Integer
d_slot'45'to'45'disp_10 v0
  = coe
      mulInt (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_112)
-- Once.CCC.Target.X86-64.AbstractToX86.compile-abstract
d_compile'45'abstract_14 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_1510 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60]
d_compile'45'abstract_14 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_1512
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_1514
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_1516
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_46
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_1518
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_112))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_1520 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbp_24)
                      (coe d_slot'45'to'45'disp_10 (coe v1)))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_1522 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbp_24)
                      (coe d_slot'45'to'45'disp_10 (coe v1))))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_1524
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_46
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_1526
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22)
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_112)))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_1528 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_lea_64
                (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12)
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbp_24)
                   (coe d_slot'45'to'45'disp_10 (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_1530 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbp_24)
                      (coe d_slot'45'to'45'disp_10 (coe v1)))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_1532 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_68
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_58
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_114
                      (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_1534 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_66
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_58
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_114
                      (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_1536 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_1538 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_push_86
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbp_24)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbp_24))
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_68
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                         (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26))
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_58
                         (coe
                            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_114
                            (coe v1))))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_1540
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbp_24)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_pop_88
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbp_24))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_1542
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call_80
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r12_36)
                      (coe
                         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_112))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_1544 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_1546 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbp_24)
                      (coe d_slot'45'to'45'disp_10 (coe v1))))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_1548 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48
                      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbp_24)
                      (coe d_slot'45'to'45'disp_10 (coe v1)))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_1550 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_1556 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.CodeGen.Compile.d_compile'45'sigOp_48
             (coe MAlonzo.Code.Once.CCC.SigOp.Info.d_name_276 (coe v3))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_1560 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.CodeGen.Compile.du_compile'45'const_60
             (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.AbstractToX86.compile-trace
d_compile'45'trace_46 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_1510] ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60]
d_compile'45'trace_46 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_compile'45'abstract_14 (coe v1))
             (coe d_compile'45'trace_46 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
