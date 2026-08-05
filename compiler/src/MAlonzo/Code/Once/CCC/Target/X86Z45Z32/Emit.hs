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
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax
import qualified MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg

-- Once.CCC.Target.X86-32.Emit.showMem
d_showMem_10 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Mem_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showMem_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base_12 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.d_showReg_26 (coe v1))
                (")" :: Data.Text.Text))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_base'43'disp_14 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("(" :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.d_showReg_26 (coe v1))
                   (")" :: Data.Text.Text)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label'45'rel_16 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (".L" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Emit.showOperand
d_showOperand_20 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Operand_18 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showOperand_20 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20 v1
        -> coe
             MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.d_showReg_26 (coe v1)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_22 v1
        -> coe d_showMem_10 (coe v1)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_24 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("$" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Emit.showLabel
d_showLabel_28 ::
  MAlonzo.Code.Once.CCC.Label.T_Label_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showLabel_28 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Label.C_once_8 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("once_" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Once.CCC.Label.C_sigop_10 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("sigops_" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("_" :: Data.Text.Text)
                   (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)))
      MAlonzo.Code.Once.CCC.Label.C_thunk_12 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("_thunk_" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Emit.showInstr
d_showInstr_38 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showInstr_38 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_20 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_20 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_lea_30 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    leal " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showMem_10 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.d_showReg_26
                      (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_push_32 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    pushl " :: Data.Text.Text)
                    (MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.d_showReg_26 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_22 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    pushl " :: Data.Text.Text) (d_showMem_10 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_24 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    pushl $" :: Data.Text.Text)
                    (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_pop_34 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    popl " :: Data.Text.Text)
             (MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.d_showReg_26 (coe v1))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_add_36 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    addl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_20 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_20 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_sub_38 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    subl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_20 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_20 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_cmp_40 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    cmpl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_20 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_20 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_test_42 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    testl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_20 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_20 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jmp_44 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    jmp *" :: Data.Text.Text)
                    (MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.d_showReg_26 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_22 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    jmp *" :: Data.Text.Text) (d_showMem_10 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_24 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    jmp " :: Data.Text.Text)
                    (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jne_46 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    jne .L" :: Data.Text.Text) (d_showLabel_28 (coe v1))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_je_48 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    je .L" :: Data.Text.Text) (d_showLabel_28 (coe v1))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call_50 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    call *" :: Data.Text.Text)
                    (MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.d_showReg_26 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mem_22 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    call *" :: Data.Text.Text) (d_showMem_10 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_24 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    call " :: Data.Text.Text)
                    (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call'45'sym_52 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    call " :: Data.Text.Text) v1
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ret_54
        -> coe ("    ret" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_nop_56
        -> coe ("    nop" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ud2_58
        -> coe ("    ud2" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label_60 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (".L" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showLabel_28 (coe v1)) (":" :: Data.Text.Text))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov'45'code_62 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movl $.L_thunk_" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.d_showReg_26
                      (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jmp'45'l_64 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    jmp .L" :: Data.Text.Text) (d_showLabel_28 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-32.Emit.instrToLine
d_instrToLine_98 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_instrToLine_98 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (d_showInstr_38 (coe v0)) ("\n" :: Data.Text.Text)
-- Once.CCC.Target.X86-32.Emit.programToText
d_programToText_102 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_programToText_102
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Data.String.Base.d__'43''43'__20
              (d_instrToLine_98 (coe v0))))
      (coe ("" :: Data.Text.Text))
