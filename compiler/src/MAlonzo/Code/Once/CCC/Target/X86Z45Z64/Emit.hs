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

module MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Emit where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax

-- Once.CCC.Target.X86-64.Emit.showReg
d_showReg_10 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Reg_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showReg_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12
        -> coe ("%rax" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbx_14
        -> coe ("%rbx" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rcx_16
        -> coe ("%rcx" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdx_18
        -> coe ("%rdx" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsi_20
        -> coe ("%rsi" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rdi_22
        -> coe ("%rdi" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rbp_24
        -> coe ("%rbp" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rsp_26
        -> coe ("%rsp" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r8_28
        -> coe ("%r8" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r9_30
        -> coe ("%r9" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r10_32
        -> coe ("%r10" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r11_34
        -> coe ("%r11" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r12_36
        -> coe ("%r12" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r13_38
        -> coe ("%r13" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r14_40
        -> coe ("%r14" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_r15_42
        -> coe ("%r15" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Emit.showMem
d_showMem_12 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Mem_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showMem_12 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_46 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showReg_10 (coe v1)) (")" :: Data.Text.Text))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_48 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("(" :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (d_showReg_10 (coe v1)) (")" :: Data.Text.Text)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rip'43'disp_50 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
             ("(%rip)" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Emit.showOperand
d_showOperand_22 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Operand_52 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showOperand_22 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54 v1
        -> coe d_showReg_10 (coe v1)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56 v1
        -> coe d_showMem_12 (coe v1)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_58 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("$" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Emit.showInstr
d_showInstr_30 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showInstr_30 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_62 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_22 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_22 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_lea_64 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    leaq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showMem_12 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showReg_10 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_66 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    addq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_22 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_22 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_68 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    subq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_22 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_22 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_cmp_70 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    cmpq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_22 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_22 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_test_72 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    testq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_22 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_22 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jmp_74 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    jmp .L" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_je_76 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    je .L" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jne_78 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    jne .L" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call_80 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    call *" :: Data.Text.Text) (d_showReg_10 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    call *" :: Data.Text.Text) (d_showMem_12 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_58 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    call " :: Data.Text.Text)
                    (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ret_82
        -> coe ("    ret" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_push_84 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_54 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    pushq " :: Data.Text.Text) (d_showReg_10 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_56 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    pushq " :: Data.Text.Text) (d_showMem_12 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_58 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    pushq $" :: Data.Text.Text)
                    (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_pop_86 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    popq " :: Data.Text.Text) (d_showReg_10 (coe v1))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_nop_88
        -> coe ("    nop" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_90
        -> coe ("    ud2" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_92 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (".L" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
                (":" :: Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Emit.instrToLine
d_instrToLine_78 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_instrToLine_78 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (d_showInstr_30 (coe v0)) ("\n" :: Data.Text.Text)
-- Once.CCC.Target.X86-64.Emit.programToText
d_programToText_82 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_60] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_programToText_82
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Data.String.Base.d__'43''43'__20
              (d_instrToLine_78 (coe v0))))
      (coe ("" :: Data.Text.Text))
