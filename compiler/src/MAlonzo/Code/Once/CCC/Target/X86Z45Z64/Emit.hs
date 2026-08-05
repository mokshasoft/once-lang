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
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg

-- Once.CCC.Target.X86-64.Emit.showMem
d_showMem_10 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Mem_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showMem_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_12 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.d_showReg_42 (coe v1))
                (")" :: Data.Text.Text))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_14 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("(" :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.d_showReg_42 (coe v1))
                   (")" :: Data.Text.Text)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rip'43'disp_16 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
             ("(%rip)" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rip'43'label_18 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (".L_thunk_" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.CCC.Label.d_showLabelId_248 (coe v1))
                ("(%rip)" :: Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Emit.showOperand
d_showOperand_22 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Operand_20 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showOperand_22 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_22 v1
        -> coe
             MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.d_showReg_42 (coe v1)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_24 v1
        -> coe d_showMem_10 (coe v1)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_26 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("$" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Emit.showLabel
d_showLabel_30 ::
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showLabel_30 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Label.C_once_24 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("once_" :: Data.Text.Text)
             (MAlonzo.Code.Once.CCC.Label.d_showLabelId_248 (coe v1))
      MAlonzo.Code.Once.CCC.Label.C_sigop_26 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("sigops_" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("_" :: Data.Text.Text)
                   (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)))
      MAlonzo.Code.Once.CCC.Label.C_thunk_28 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("_thunk_" :: Data.Text.Text)
             (MAlonzo.Code.Once.CCC.Label.d_showLabelId_248 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Emit.showInstr
d_showInstr_40 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showInstr_40 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_30 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_22 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_22 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_lea_32 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    leaq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showMem_10 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.d_showReg_42
                      (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_34 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    addq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_22 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_22 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_36 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    subq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_22 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_22 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_cmp_38 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    cmpq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_22 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_22 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_test_40 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    testq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_22 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_22 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jmp_42 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    jmp .L" :: Data.Text.Text) (d_showLabel_30 (coe v1))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_je_44 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    je .L" :: Data.Text.Text) (d_showLabel_30 (coe v1))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jne_46 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    jne .L" :: Data.Text.Text) (d_showLabel_30 (coe v1))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call_48 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_22 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    call *" :: Data.Text.Text)
                    (MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.d_showReg_42 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_24 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    call *" :: Data.Text.Text) (d_showMem_10 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_26 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    call " :: Data.Text.Text)
                    (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call'45'sym_50 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    call " :: Data.Text.Text) v1
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ret_52
        -> coe ("    ret" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_push_54 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_22 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    pushq " :: Data.Text.Text)
                    (MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.d_showReg_42 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_24 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    pushq " :: Data.Text.Text) (d_showMem_10 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_26 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    pushq $" :: Data.Text.Text)
                    (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_pop_56 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    popq " :: Data.Text.Text)
             (MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.d_showReg_42 (coe v1))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_nop_58
        -> coe ("    nop" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_60
        -> coe ("    ud2" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_syscall_62
        -> coe ("    syscall" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_64 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (".L" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showLabel_30 (coe v1)) (":" :: Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Emit.instrToLine
d_instrToLine_90 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_instrToLine_90 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (d_showInstr_40 (coe v0)) ("\n" :: Data.Text.Text)
-- Once.CCC.Target.X86-64.Emit.programToText
d_programToText_94 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_programToText_94
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Data.String.Base.d__'43''43'__20
              (d_instrToLine_90 (coe v0))))
      (coe ("" :: Data.Text.Text))
