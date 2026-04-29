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

module MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Emit where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax

-- Once.CCC.Target.X86-32.Emit.showReg
d_showReg_10 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Reg_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showReg_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_eax_12
        -> coe ("%eax" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ebx_14
        -> coe ("%ebx" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ecx_16
        -> coe ("%ecx" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_edx_18
        -> coe ("%edx" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_esi_20
        -> coe ("%esi" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_edi_22
        -> coe ("%edi" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ebp_24
        -> coe ("%ebp" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_esp_26
        -> coe ("%esp" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Emit.showMem
d_showMem_12 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Mem_28 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showMem_12 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base_30 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showReg_10 (coe v1)) (")" :: Data.Text.Text))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_32 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("(" :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (d_showReg_10 (coe v1)) (")" :: Data.Text.Text)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label'45'rel_34 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (".L" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Emit.showOperand
d_showOperand_22 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Operand_36 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showOperand_22 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_38 v1
        -> coe d_showReg_10 (coe v1)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_40 v1
        -> coe d_showMem_12 (coe v1)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_42 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("$" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Emit.showInstr
d_showInstr_30 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showInstr_30 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_46 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_22 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_22 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_lea_48 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    leal " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showMem_12 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showReg_10 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_push_50 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_38 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    pushl " :: Data.Text.Text) (d_showReg_10 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_40 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    pushl " :: Data.Text.Text) (d_showMem_12 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_42 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    pushl $" :: Data.Text.Text)
                    (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_pop_52 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    popl " :: Data.Text.Text) (d_showReg_10 (coe v1))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_add_54 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    addl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_22 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_22 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_sub_56 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    subl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_22 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_22 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_cmp_58 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    cmpl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_22 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_22 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_test_60 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    testl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_22 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_22 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jmp_62 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_38 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    jmp *" :: Data.Text.Text) (d_showReg_10 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_40 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    jmp *" :: Data.Text.Text) (d_showMem_12 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_42 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    jmp " :: Data.Text.Text)
                    (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jne_64 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    jne .L" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_je_66 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    je .L" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call_68 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_38 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    call *" :: Data.Text.Text) (d_showReg_10 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_40 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    call *" :: Data.Text.Text) (d_showMem_12 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_42 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    call " :: Data.Text.Text)
                    (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call'45'sym_70 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    call " :: Data.Text.Text) v1
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ret_72
        -> coe ("    ret" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_nop_74
        -> coe ("    nop" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ud2_76
        -> coe ("    ud2" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label_78 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (".L" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
                (":" :: Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Emit.instrToLine
d_instrToLine_84 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_instrToLine_84 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (d_showInstr_30 (coe v0)) ("\n" :: Data.Text.Text)
-- Once.CCC.Target.X86-32.Emit.programToText
d_programToText_88 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_44] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_programToText_88
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Data.String.Base.d__'43''43'__20
              (d_instrToLine_84 (coe v0))))
      (coe ("" :: Data.Text.Text))
