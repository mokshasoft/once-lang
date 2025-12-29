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

module MAlonzo.Code.Once.Arith.Backend.X86.Emit where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Integer.Show
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Arith.Backend.X86.Syntax

-- Once.Arith.Backend.X86.Emit.unlines
d_unlines_10 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_unlines_10 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("\n" :: Data.Text.Text) (d_unlines_10 (coe v2))) in
           coe
             (case coe v2 of
                [] -> coe v1
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.Emit.gprToText
d_gprToText_18 ::
  MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_GPReg_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_gprToText_18 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rax_12
        -> coe ("%rax" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rbx_14
        -> coe ("%rbx" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rcx_16
        -> coe ("%rcx" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rdx_18
        -> coe ("%rdx" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rsi_20
        -> coe ("%rsi" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rdi_22
        -> coe ("%rdi" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_r8_24
        -> coe ("%r8" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_r9_26
        -> coe ("%r9" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_r10_28
        -> coe ("%r10" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_r11_30
        -> coe ("%r11" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.Emit.gpr8ToText
d_gpr8ToText_20 ::
  MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_GPReg_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_gpr8ToText_20 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rax_12
        -> coe ("%al" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rbx_14
        -> coe ("%bl" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rcx_16
        -> coe ("%cl" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rdx_18
        -> coe ("%dl" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rsi_20
        -> coe ("%sil" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rdi_22
        -> coe ("%dil" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_r8_24
        -> coe ("%r8b" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_r9_26
        -> coe ("%r9b" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_r10_28
        -> coe ("%r10b" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_r11_30
        -> coe ("%r11b" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.Emit.xmmToText
d_xmmToText_22 ::
  MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_XMMReg_90 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_xmmToText_22 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm0_92
        -> coe ("%xmm0" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm1_94
        -> coe ("%xmm1" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm2_96
        -> coe ("%xmm2" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm3_98
        -> coe ("%xmm3" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm4_100
        -> coe ("%xmm4" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm5_102
        -> coe ("%xmm5" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm6_104
        -> coe ("%xmm6" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm7_106
        -> coe ("%xmm7" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm8_108
        -> coe ("%xmm8" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm9_110
        -> coe ("%xmm9" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm10_112
        -> coe ("%xmm10" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm11_114
        -> coe ("%xmm11" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm12_116
        -> coe ("%xmm12" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm13_118
        -> coe ("%xmm13" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm14_120
        -> coe ("%xmm14" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm15_122
        -> coe ("%xmm15" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.Emit.memToText
d_memToText_24 ::
  MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_ArithMem_130 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_memToText_24 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_base_132 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1)) (")" :: Data.Text.Text))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_base'43'disp_134 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("(" :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (d_gprToText_18 (coe v1)) (")" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.Emit.intOpToText
d_intOpToText_32 ::
  MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_IntOperand_136 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_intOpToText_32 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regI_138 v1
        -> coe d_gprToText_18 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_memI_140 v1
        -> coe d_memToText_24 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_immI_142 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("$" :: Data.Text.Text)
             (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.Emit.floatOpToText
d_floatOpToText_40 ::
  MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_FloatOperand_144 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_floatOpToText_40 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regF_146 v1
        -> coe d_xmmToText_22 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_memF_148 v1
        -> coe d_memToText_24 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.Emit.ccToText
d_ccToText_46 ::
  MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_CondCode_150 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_ccToText_46 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_cc'45'e_152
        -> coe ("e" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_cc'45'ne_154
        -> coe ("ne" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_cc'45'l_156
        -> coe ("l" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_cc'45'le_158
        -> coe ("le" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_cc'45'g_160
        -> coe ("g" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_cc'45'ge_162
        -> coe ("ge" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.Emit.intInstrToText
d_intInstrToText_48 ::
  MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_IntInstr_164 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_intInstrToText_48 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movI_166 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_intOpToText_32 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_gprToText_18 (coe v1))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_addI_168 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    addq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_intOpToText_32 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_gprToText_18 (coe v1))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_subI_170 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    subq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_intOpToText_32 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_gprToText_18 (coe v1))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_imulI_172 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    imulq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_intOpToText_32 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_gprToText_18 (coe v1))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_negI_174 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    negq " :: Data.Text.Text) (d_gprToText_18 (coe v1))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_cqo_176
        -> coe ("    cqo" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_idivI_178 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    idivq " :: Data.Text.Text) (d_intOpToText_32 (coe v1))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_pushI_180 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    pushq " :: Data.Text.Text) (d_gprToText_18 (coe v1))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_popI_182 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    popq " :: Data.Text.Text) (d_gprToText_18 (coe v1))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_cmpI_184 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    cmpq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_intOpToText_32 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_gprToText_18 (coe v1))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_setccI_186 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    set" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_ccToText_46 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text) (d_gpr8ToText_20 (coe v2))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movzxI_188 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movzbl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gpr8ToText_20 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_gprToText_18 (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.Emit.floatInstrToText
d_floatInstrToText_86 ::
  MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_FloatInstr_190 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_floatInstrToText_86 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movss_192 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movss " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_floatOpToText_40 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_xmmToText_22 (coe v1))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movsd_194 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movsd " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_floatOpToText_40 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_xmmToText_22 (coe v1))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_addss_196 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    addss " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_floatOpToText_40 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_xmmToText_22 (coe v1))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_subss_198 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    subss " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_floatOpToText_40 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_xmmToText_22 (coe v1))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_mulss_200 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    mulss " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_floatOpToText_40 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_xmmToText_22 (coe v1))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_divss_202 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    divss " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_floatOpToText_40 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_xmmToText_22 (coe v1))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_addsd_204 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    addsd " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_floatOpToText_40 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_xmmToText_22 (coe v1))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_subsd_206 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    subsd " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_floatOpToText_40 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_xmmToText_22 (coe v1))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_mulsd_208 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    mulsd " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_floatOpToText_40 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_xmmToText_22 (coe v1))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_divsd_210 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    divsd " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_floatOpToText_40 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_xmmToText_22 (coe v1))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xorps_212 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    xorps " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_xmmToText_22 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_xmmToText_22 (coe v1))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xorpd_214 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    xorpd " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_xmmToText_22 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_xmmToText_22 (coe v1))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movqToXMM_216 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_xmmToText_22 (coe v1))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_cvtss2sd_218 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    cvtss2sd " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_xmmToText_22 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_xmmToText_22 (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.Emit.instrToText
d_instrToText_144 ::
  MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_ArithInstr_220 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_instrToText_144 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222 v1
        -> coe d_intInstrToText_48 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224 v1
        -> coe d_floatInstrToText_86 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.Emit.emitProgram
d_emitProgram_150 ::
  [MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_ArithInstr_220] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emitProgram_150 v0
  = coe
      d_unlines_10
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22 (coe d_instrToText_144)
         (coe v0))
