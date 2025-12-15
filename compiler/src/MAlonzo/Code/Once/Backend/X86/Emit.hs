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

module MAlonzo.Code.Once.Backend.X86.Emit where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Backend.X86.Syntax

-- Once.Backend.X86.Emit.unlines
d_unlines_8 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_unlines_8 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("\n" :: Data.Text.Text) (d_unlines_8 (coe v2))) in
           coe
             (case coe v2 of
                [] -> coe v1
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.X86.Emit.regToText
d_regToText_16 ::
  MAlonzo.Code.Once.Backend.X86.Syntax.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_regToText_16 v0
  = case coe v0 of
      MAlonzo.Code.Once.Backend.X86.Syntax.C_rax_10
        -> coe ("%rax" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.X86.Syntax.C_rbx_12
        -> coe ("%rbx" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.X86.Syntax.C_rcx_14
        -> coe ("%rcx" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.X86.Syntax.C_rdx_16
        -> coe ("%rdx" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.X86.Syntax.C_rsi_18
        -> coe ("%rsi" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20
        -> coe ("%rdi" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.X86.Syntax.C_rbp_22
        -> coe ("%rbp" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24
        -> coe ("%rsp" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.X86.Syntax.C_r8_26
        -> coe ("%r8" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.X86.Syntax.C_r9_28
        -> coe ("%r9" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.X86.Syntax.C_r10_30
        -> coe ("%r10" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.X86.Syntax.C_r11_32
        -> coe ("%r11" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.X86.Syntax.C_r12_34
        -> coe ("%r12" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.X86.Syntax.C_r13_36
        -> coe ("%r13" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.X86.Syntax.C_r14_38
        -> coe ("%r14" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.X86.Syntax.C_r15_40
        -> coe ("%r15" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.X86.Emit.memToText
d_memToText_18 ::
  MAlonzo.Code.Once.Backend.X86.Syntax.T_Mem_42 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_memToText_18 v0
  = case coe v0 of
      MAlonzo.Code.Once.Backend.X86.Syntax.C_base_44 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_16 (coe v1)) (")" :: Data.Text.Text))
      MAlonzo.Code.Once.Backend.X86.Syntax.C_base'43'disp_46 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("(" :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (d_regToText_16 (coe v1)) (")" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.X86.Emit.operandToText
d_operandToText_26 ::
  MAlonzo.Code.Once.Backend.X86.Syntax.T_Operand_48 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_operandToText_26 v0
  = case coe v0 of
      MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_50 v1
        -> coe d_regToText_16 (coe v1)
      MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_52 v1
        -> coe d_memToText_18 (coe v1)
      MAlonzo.Code.Once.Backend.X86.Syntax.C_imm_54 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("$" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.X86.Emit.instrToText
d_instrToText_34 ::
  MAlonzo.Code.Once.Backend.X86.Syntax.T_Instr_56 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_instrToText_34 v0
  = case coe v0 of
      MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_58 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_operandToText_26 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_operandToText_26 (coe v1))))
      MAlonzo.Code.Once.Backend.X86.Syntax.C_lea_60 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    leaq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_memToText_18 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_regToText_16 (coe v1))))
      MAlonzo.Code.Once.Backend.X86.Syntax.C_add_62 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    addq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_operandToText_26 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_operandToText_26 (coe v1))))
      MAlonzo.Code.Once.Backend.X86.Syntax.C_sub_64 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    subq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_operandToText_26 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_operandToText_26 (coe v1))))
      MAlonzo.Code.Once.Backend.X86.Syntax.C_cmp_66 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    cmpq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_operandToText_26 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_operandToText_26 (coe v1))))
      MAlonzo.Code.Once.Backend.X86.Syntax.C_test_68 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    testq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_operandToText_26 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_operandToText_26 (coe v1))))
      MAlonzo.Code.Once.Backend.X86.Syntax.C_jmp_70 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    jmp .L" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Once.Backend.X86.Syntax.C_je_72 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    je .L" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Once.Backend.X86.Syntax.C_jne_74 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    jne .L" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Once.Backend.X86.Syntax.C_call_76 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    call *" :: Data.Text.Text) (d_operandToText_26 (coe v1))
      MAlonzo.Code.Once.Backend.X86.Syntax.C_ret_78
        -> coe ("    ret" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.X86.Syntax.C_push_80 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    pushq " :: Data.Text.Text) (d_operandToText_26 (coe v1))
      MAlonzo.Code.Once.Backend.X86.Syntax.C_pop_82 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    popq " :: Data.Text.Text) (d_regToText_16 (coe v1))
      MAlonzo.Code.Once.Backend.X86.Syntax.C_nop_84
        -> coe ("    nop" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.X86.Syntax.C_ud2_86
        -> coe ("    ud2" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.X86.Syntax.C_label_88 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (".L" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
                (":" :: Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.X86.Emit.programToText
d_programToText_74 ::
  [MAlonzo.Code.Once.Backend.X86.Syntax.T_Instr_56] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_programToText_74 v0
  = coe
      d_unlines_8
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22 (coe d_instrToText_34)
         (coe v0))
