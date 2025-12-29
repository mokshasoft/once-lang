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

module MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

-- Once.Arith.Backend.AArch64.Syntax.GPReg
d_GPReg_10 = ()
data T_GPReg_10
  = C_x0_12 | C_x1_14 | C_x2_16 | C_x3_18 | C_x4_20 | C_x5_22 |
    C_x6_24 | C_x7_26 | C_x8_28 | C_x9_30 | C_x10_32 | C_x11_34 |
    C_x12_36 | C_x13_38 | C_x14_40 | C_x15_42 | C_x16_44 | C_x17_46 |
    C_x18_48 | C_x19_50 | C_x20_52 | C_x21_54 | C_x22_56 | C_x23_58 |
    C_x24_60 | C_x25_62 | C_x26_64 | C_x27_66 | C_x28_68 | C_x29_70 |
    C_x30_72
-- Once.Arith.Backend.AArch64.Syntax.FPReg
d_FPReg_74 = ()
data T_FPReg_74
  = C_d0_76 | C_d1_78 | C_d2_80 | C_d3_82 | C_d4_84 | C_d5_86 |
    C_d6_88 | C_d7_90 | C_d8_92 | C_d9_94 | C_d10_96 | C_d11_98 |
    C_d12_100 | C_d13_102 | C_d14_104 | C_d15_106 | C_d16_108 |
    C_d17_110 | C_d18_112 | C_d19_114 | C_d20_116 | C_d21_118 |
    C_d22_120 | C_d23_122 | C_d24_124 | C_d25_126 | C_d26_128 |
    C_d27_130 | C_d28_132 | C_d29_134 | C_d30_136 | C_d31_138
-- Once.Arith.Backend.AArch64.Syntax.Reg
d_Reg_140 a0 = ()
data T_Reg_140 = C_gpr_142 T_GPReg_10 | C_fp_144 T_FPReg_74
-- Once.Arith.Backend.AArch64.Syntax.Operand
d_Operand_146 = ()
data T_Operand_146 = C_regOp_148 T_GPReg_10 | C_immOp_150 Integer
-- Once.Arith.Backend.AArch64.Syntax.FPOperand
d_FPOperand_152 = ()
newtype T_FPOperand_152 = C_fpRegOp_154 T_FPReg_74
-- Once.Arith.Backend.AArch64.Syntax.Cond
d_Cond_156 = ()
data T_Cond_156
  = C_cond'45'eq_158 | C_cond'45'ne_160 | C_cond'45'lt_162 |
    C_cond'45'le_164 | C_cond'45'gt_166 | C_cond'45'ge_168
-- Once.Arith.Backend.AArch64.Syntax.IntInstr
d_IntInstr_170 = ()
data T_IntInstr_170
  = C_mov_172 T_GPReg_10 T_Operand_146 |
    C_movz_174 T_GPReg_10 Integer Integer |
    C_movk_176 T_GPReg_10 Integer Integer |
    C_add_178 T_GPReg_10 T_GPReg_10 T_Operand_146 |
    C_sub_180 T_GPReg_10 T_GPReg_10 T_Operand_146 |
    C_mul_182 T_GPReg_10 T_GPReg_10 T_GPReg_10 |
    C_sdiv_184 T_GPReg_10 T_GPReg_10 T_GPReg_10 |
    C_msub_186 T_GPReg_10 T_GPReg_10 T_GPReg_10 T_GPReg_10 |
    C_neg_188 T_GPReg_10 T_GPReg_10 | C_strPre_190 T_GPReg_10 Integer |
    C_ldrPost_192 T_GPReg_10 Integer |
    C_cmp_194 T_GPReg_10 T_Operand_146 |
    C_cset_196 T_GPReg_10 T_Cond_156
-- Once.Arith.Backend.AArch64.Syntax.FPInstr
d_FPInstr_198 = ()
data T_FPInstr_198
  = C_fmov_200 T_FPReg_74 T_FPOperand_152 |
    C_fadd_202 T_FPReg_74 T_FPReg_74 T_FPReg_74 |
    C_fsub_204 T_FPReg_74 T_FPReg_74 T_FPReg_74 |
    C_fmul_206 T_FPReg_74 T_FPReg_74 T_FPReg_74 |
    C_fdiv_208 T_FPReg_74 T_FPReg_74 T_FPReg_74 |
    C_fneg_210 T_FPReg_74 T_FPReg_74 |
    C_faddS_212 T_FPReg_74 T_FPReg_74 T_FPReg_74 |
    C_fsubS_214 T_FPReg_74 T_FPReg_74 T_FPReg_74 |
    C_fmulS_216 T_FPReg_74 T_FPReg_74 T_FPReg_74 |
    C_fdivS_218 T_FPReg_74 T_FPReg_74 T_FPReg_74 |
    C_fnegS_220 T_FPReg_74 T_FPReg_74 |
    C_fcvtSD_222 T_FPReg_74 T_FPReg_74
-- Once.Arith.Backend.AArch64.Syntax.ArithInstr
d_ArithInstr_224 = ()
data T_ArithInstr_224
  = C_intI_226 T_IntInstr_170 | C_fpI_228 T_FPInstr_198
-- Once.Arith.Backend.AArch64.Syntax.ArithProgram
d_ArithProgram_230 :: ()
d_ArithProgram_230 = erased
