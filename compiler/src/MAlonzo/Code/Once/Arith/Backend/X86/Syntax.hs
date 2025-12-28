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

module MAlonzo.Code.Once.Arith.Backend.X86.Syntax where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

-- Once.Arith.Backend.X86.Syntax.GPReg
d_GPReg_10 = ()
data T_GPReg_10
  = C_rax_12 | C_rbx_14 | C_rcx_16 | C_rdx_18 | C_rsi_20 | C_rdi_22 |
    C_r8_24 | C_r9_26 | C_r10_28 | C_r11_30
-- Once.Arith.Backend.X86.Syntax.GPR32
d_GPR32_32 = ()
data T_GPR32_32
  = C_eax_34 | C_ebx_36 | C_ecx_38 | C_edx_40 | C_esi_42 | C_edi_44 |
    C_r8d_46 | C_r9d_48 | C_r10d_50 | C_r11d_52
-- Once.Arith.Backend.X86.Syntax.GPR16
d_GPR16_54 = ()
data T_GPR16_54
  = C_ax_56 | C_bx_58 | C_cx_60 | C_dx_62 | C_si_64 | C_di_66
-- Once.Arith.Backend.X86.Syntax.GPR8
d_GPR8_68 = ()
data T_GPR8_68
  = C_al_70 | C_bl_72 | C_cl_74 | C_dl_76 | C_sil_78 | C_dil_80 |
    C_r8b_82 | C_r9b_84 | C_r10b_86 | C_r11b_88
-- Once.Arith.Backend.X86.Syntax.XMMReg
d_XMMReg_90 = ()
data T_XMMReg_90
  = C_xmm0_92 | C_xmm1_94 | C_xmm2_96 | C_xmm3_98 | C_xmm4_100 |
    C_xmm5_102 | C_xmm6_104 | C_xmm7_106 | C_xmm8_108 | C_xmm9_110 |
    C_xmm10_112 | C_xmm11_114 | C_xmm12_116 | C_xmm13_118 |
    C_xmm14_120 | C_xmm15_122
-- Once.Arith.Backend.X86.Syntax.Reg
d_Reg_124 a0 = ()
data T_Reg_124 = C_gpr_126 T_GPReg_10 | C_xmm_128 T_XMMReg_90
-- Once.Arith.Backend.X86.Syntax.ArithMem
d_ArithMem_130 = ()
data T_ArithMem_130
  = C_base_132 T_GPReg_10 | C_base'43'disp_134 T_GPReg_10 Integer
-- Once.Arith.Backend.X86.Syntax.IntOperand
d_IntOperand_136 = ()
data T_IntOperand_136
  = C_regI_138 T_GPReg_10 | C_memI_140 T_ArithMem_130 |
    C_immI_142 Integer
-- Once.Arith.Backend.X86.Syntax.FloatOperand
d_FloatOperand_144 = ()
data T_FloatOperand_144
  = C_regF_146 T_XMMReg_90 | C_memF_148 T_ArithMem_130
-- Once.Arith.Backend.X86.Syntax.CondCode
d_CondCode_150 = ()
data T_CondCode_150
  = C_cc'45'e_152 | C_cc'45'ne_154 | C_cc'45'l_156 | C_cc'45'le_158 |
    C_cc'45'g_160 | C_cc'45'ge_162
-- Once.Arith.Backend.X86.Syntax.IntInstr
d_IntInstr_164 = ()
data T_IntInstr_164
  = C_movI_166 T_GPReg_10 T_IntOperand_136 |
    C_addI_168 T_GPReg_10 T_IntOperand_136 |
    C_subI_170 T_GPReg_10 T_IntOperand_136 |
    C_imulI_172 T_GPReg_10 T_IntOperand_136 | C_negI_174 T_GPReg_10 |
    C_cqo_176 | C_idivI_178 T_IntOperand_136 | C_pushI_180 T_GPReg_10 |
    C_popI_182 T_GPReg_10 | C_cmpI_184 T_GPReg_10 T_IntOperand_136 |
    C_setccI_186 T_CondCode_150 T_GPReg_10 |
    C_movzxI_188 T_GPReg_10 T_GPReg_10
-- Once.Arith.Backend.X86.Syntax.FloatInstr
d_FloatInstr_190 = ()
data T_FloatInstr_190
  = C_movss_192 T_XMMReg_90 T_FloatOperand_144 |
    C_movsd_194 T_XMMReg_90 T_FloatOperand_144 |
    C_addss_196 T_XMMReg_90 T_FloatOperand_144 |
    C_subss_198 T_XMMReg_90 T_FloatOperand_144 |
    C_mulss_200 T_XMMReg_90 T_FloatOperand_144 |
    C_divss_202 T_XMMReg_90 T_FloatOperand_144 |
    C_addsd_204 T_XMMReg_90 T_FloatOperand_144 |
    C_subsd_206 T_XMMReg_90 T_FloatOperand_144 |
    C_mulsd_208 T_XMMReg_90 T_FloatOperand_144 |
    C_divsd_210 T_XMMReg_90 T_FloatOperand_144 |
    C_xorps_212 T_XMMReg_90 T_XMMReg_90 |
    C_xorpd_214 T_XMMReg_90 T_XMMReg_90 |
    C_movqToXMM_216 T_XMMReg_90 T_GPReg_10
-- Once.Arith.Backend.X86.Syntax.ArithInstr
d_ArithInstr_218 = ()
data T_ArithInstr_218
  = C_intI_220 T_IntInstr_164 | C_floatI_222 T_FloatInstr_190
-- Once.Arith.Backend.X86.Syntax.ArithProgram
d_ArithProgram_224 :: ()
d_ArithProgram_224 = erased
