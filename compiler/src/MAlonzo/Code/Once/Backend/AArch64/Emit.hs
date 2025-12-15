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

module MAlonzo.Code.Once.Backend.AArch64.Emit where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Backend.AArch64.Syntax

-- Once.Backend.AArch64.Emit.unlines
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
-- Once.Backend.AArch64.Emit.regToText
d_regToText_16 ::
  MAlonzo.Code.Once.Backend.AArch64.Syntax.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_regToText_16 v0
  = case coe v0 of
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10
        -> coe ("x0" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x1_12
        -> coe ("x1" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x2_14
        -> coe ("x2" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x3_16
        -> coe ("x3" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x4_18
        -> coe ("x4" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x5_20
        -> coe ("x5" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x6_22
        -> coe ("x6" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x7_24
        -> coe ("x7" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x8_26
        -> coe ("x8" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28
        -> coe ("x9" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x10_30
        -> coe ("x10" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x11_32
        -> coe ("x11" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x12_34
        -> coe ("x12" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x13_36
        -> coe ("x13" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x14_38
        -> coe ("x14" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x15_40
        -> coe ("x15" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x16_42
        -> coe ("x16" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x17_44
        -> coe ("x17" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x18_46
        -> coe ("x18" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x19_48
        -> coe ("x19" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x20_50
        -> coe ("x20" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x21_52
        -> coe ("x21" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x22_54
        -> coe ("x22" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x23_56
        -> coe ("x23" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x24_58
        -> coe ("x24" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x25_60
        -> coe ("x25" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x26_62
        -> coe ("x26" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x27_64
        -> coe ("x27" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x28_66
        -> coe ("x28" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x29_68
        -> coe ("x29" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x30_70
        -> coe ("x30" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.AArch64.Emit.memToText
d_memToText_18 ::
  MAlonzo.Code.Once.Backend.AArch64.Syntax.T_Mem_72 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_memToText_18 v0
  = case coe v0 of
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base_74 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("[" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_16 (coe v1)) ("]" :: Data.Text.Text))
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base'43'imm_76 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("[" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", #" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
                      ("]" :: Data.Text.Text))))
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sp'43'imm_78 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("[sp, #" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
                ("]" :: Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.AArch64.Emit.operandToText
d_operandToText_28 ::
  MAlonzo.Code.Once.Backend.AArch64.Syntax.T_Operand_80 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_operandToText_28 v0
  = case coe v0 of
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_reg_82 v1
        -> coe d_regToText_16 (coe v1)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mem_84 v1
        -> coe d_memToText_18 (coe v1)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_imm_86 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("#" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.AArch64.Emit.instrToText
d_instrToText_36 ::
  MAlonzo.Code.Once.Backend.AArch64.Syntax.T_Instr_88 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_instrToText_36 v0
  = case coe v0 of
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov_90 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    mov " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_operandToText_28 (coe v2))))
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ldr_92 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    ldr " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_memToText_18 (coe v2))))
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_str_94 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    str " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_memToText_18 (coe v2))))
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ldp_96 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    ldp " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_16 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_memToText_18 (coe v3))))))
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_stp_98 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    stp " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_16 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_memToText_18 (coe v3))))))
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_add_100 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    add " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_16 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_operandToText_28 (coe v3))))))
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sub_102 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    sub " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_16 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_operandToText_28 (coe v3))))))
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_cmp_104 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    cmp " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_operandToText_28 (coe v2))))
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_b_106 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    b .L" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_b'45'eq_108 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    b.eq .L" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_b'45'ne_110 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    b.ne .L" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_bl_112 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    bl .L" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_blr_114 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    blr " :: Data.Text.Text) (d_regToText_16 (coe v1))
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ret_116
        -> coe ("    ret" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sub'45'sp_118 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    sub sp, sp, #" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_add'45'sp_120 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    add sp, sp, #" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov'45'from'45'sp_122 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    mov " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_16 (coe v1)) (", sp" :: Data.Text.Text))
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_nop_124
        -> coe ("    nop" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_brk_126 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    brk #" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_str'45'zr_128 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    str xzr, " :: Data.Text.Text) (d_memToText_18 (coe v1))
      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_label_130 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (".L" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
                (":" :: Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.AArch64.Emit.programToText
d_programToText_100 ::
  [MAlonzo.Code.Once.Backend.AArch64.Syntax.T_Instr_88] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_programToText_100 v0
  = coe
      d_unlines_8
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22 (coe d_instrToText_36)
         (coe v0))
