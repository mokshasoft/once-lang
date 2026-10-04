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
             (MAlonzo.Code.Once.CCC.Label.d_thunkSym_388 (coe v1))
             ("(%rip)" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rip'43'sym_20 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
             ("(%rip)" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Emit.showOperand
d_showOperand_24 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Operand_22 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showOperand_24 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24 v1
        -> coe
             MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.d_showReg_42 (coe v1)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_26 v1
        -> coe d_showMem_10 (coe v1)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_28 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("$" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Emit.showInstr
d_showInstr_32 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showInstr_32 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_32 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_24 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_24 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_lea_34 v1 v2
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
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_36 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    addq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_24 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_24 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_38 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    subq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_24 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_24 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sbb_40 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    sbbq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_24 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_24 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_cmp_42 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    cmpq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_24 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_24 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_test_44 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    testq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showOperand_24 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showOperand_24 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jmp_46 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    jmp " :: Data.Text.Text)
             (MAlonzo.Code.Once.CCC.Label.d_labelSym_398 (coe v1))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_je_48 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    je " :: Data.Text.Text)
             (MAlonzo.Code.Once.CCC.Label.d_labelSym_398 (coe v1))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jne_50 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    jne " :: Data.Text.Text)
             (MAlonzo.Code.Once.CCC.Label.d_labelSym_398 (coe v1))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call_52 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    call *" :: Data.Text.Text)
                    (MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.d_showReg_42 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_26 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    call *" :: Data.Text.Text) (d_showMem_10 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_28 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    call " :: Data.Text.Text)
                    (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call'45'sym_54 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    call " :: Data.Text.Text) v1
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call'45'l_56 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    call " :: Data.Text.Text)
             (MAlonzo.Code.Once.CCC.Label.d_labelSym_398 (coe v1))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ret_58
        -> coe ("    ret" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_push_60 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    pushq " :: Data.Text.Text)
                    (MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.d_showReg_42 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_26 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    pushq " :: Data.Text.Text) (d_showMem_10 (coe v2))
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_28 v2
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    pushq $" :: Data.Text.Text)
                    (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_pop_62 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    popq " :: Data.Text.Text)
             (MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.d_showReg_42 (coe v1))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_nop_64
        -> coe ("    nop" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_66
        -> coe ("    ud2" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_syscall_68
        -> coe ("    syscall" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_70 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (MAlonzo.Code.Once.CCC.Label.d_labelSym_398 (coe v1))
             (":" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Emit.instrToLine
d_instrToLine_88 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_instrToLine_88 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (d_showInstr_32 (coe v0)) ("\n" :: Data.Text.Text)
-- Once.CCC.Target.X86-64.Emit.programToText
d_programToText_92 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_programToText_92
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Data.String.Base.d__'43''43'__20
              (d_instrToLine_88 (coe v0))))
      (coe ("" :: Data.Text.Text))
