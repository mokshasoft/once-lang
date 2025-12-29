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

module MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

-- Once.Arith.Backend.RiscV.Syntax.GPReg
d_GPReg_10 = ()
data T_GPReg_10
  = C_x0_12 | C_x1_14 | C_x2_16 | C_x3_18 | C_x4_20 | C_x5_22 |
    C_x6_24 | C_x7_26 | C_x8_28 | C_x9_30 | C_x10_32 | C_x11_34 |
    C_x12_36 | C_x13_38 | C_x14_40 | C_x15_42 | C_x16_44 | C_x17_46 |
    C_x18_48 | C_x19_50 | C_x20_52 | C_x21_54 | C_x22_56 | C_x23_58 |
    C_x24_60 | C_x25_62 | C_x26_64 | C_x27_66 | C_x28_68 | C_x29_70 |
    C_x30_72 | C_x31_74
-- Once.Arith.Backend.RiscV.Syntax.FPReg
d_FPReg_76 = ()
data T_FPReg_76
  = C_f0_78 | C_f1_80 | C_f2_82 | C_f3_84 | C_f4_86 | C_f5_88 |
    C_f6_90 | C_f7_92 | C_f8_94 | C_f9_96 | C_f10_98 | C_f11_100 |
    C_f12_102 | C_f13_104 | C_f14_106 | C_f15_108 | C_f16_110 |
    C_f17_112 | C_f18_114 | C_f19_116 | C_f20_118 | C_f21_120 |
    C_f22_122 | C_f23_124 | C_f24_126 | C_f25_128 | C_f26_130 |
    C_f27_132 | C_f28_134 | C_f29_136 | C_f30_138 | C_f31_140
-- Once.Arith.Backend.RiscV.Syntax.Reg
d_Reg_142 a0 = ()
data T_Reg_142 = C_gpr_144 T_GPReg_10 | C_fp_146 T_FPReg_76
-- Once.Arith.Backend.RiscV.Syntax.Operand
d_Operand_148 = ()
data T_Operand_148 = C_regOp_150 T_GPReg_10 | C_immOp_152 Integer
-- Once.Arith.Backend.RiscV.Syntax.FPOperand
d_FPOperand_154 = ()
newtype T_FPOperand_154 = C_fpRegOp_156 T_FPReg_76
-- Once.Arith.Backend.RiscV.Syntax.IntInstr
d_IntInstr_158 = ()
data T_IntInstr_158
  = C_li_160 T_GPReg_10 Integer | C_mv_162 T_GPReg_10 T_GPReg_10 |
    C_add_164 T_GPReg_10 T_GPReg_10 T_GPReg_10 |
    C_addi_166 T_GPReg_10 T_GPReg_10 Integer |
    C_sub_168 T_GPReg_10 T_GPReg_10 T_GPReg_10 |
    C_mul_170 T_GPReg_10 T_GPReg_10 T_GPReg_10 |
    C_div_172 T_GPReg_10 T_GPReg_10 T_GPReg_10 |
    C_rem_174 T_GPReg_10 T_GPReg_10 T_GPReg_10 |
    C_neg_176 T_GPReg_10 T_GPReg_10 | C_sd_178 T_GPReg_10 Integer |
    C_ld_180 T_GPReg_10 Integer |
    C_slt_182 T_GPReg_10 T_GPReg_10 T_GPReg_10 |
    C_sltu_184 T_GPReg_10 T_GPReg_10 T_GPReg_10 |
    C_slti_186 T_GPReg_10 T_GPReg_10 Integer |
    C_sltiu_188 T_GPReg_10 T_GPReg_10 Integer |
    C_xori_190 T_GPReg_10 T_GPReg_10 Integer |
    C_seqz_192 T_GPReg_10 T_GPReg_10 | C_snez_194 T_GPReg_10 T_GPReg_10
-- Once.Arith.Backend.RiscV.Syntax.FPInstr
d_FPInstr_196 = ()
data T_FPInstr_196
  = C_fmvD_198 T_FPReg_76 T_FPReg_76 |
    C_faddD_200 T_FPReg_76 T_FPReg_76 T_FPReg_76 |
    C_fsubD_202 T_FPReg_76 T_FPReg_76 T_FPReg_76 |
    C_fmulD_204 T_FPReg_76 T_FPReg_76 T_FPReg_76 |
    C_fdivD_206 T_FPReg_76 T_FPReg_76 T_FPReg_76 |
    C_fnegD_208 T_FPReg_76 T_FPReg_76 |
    C_faddS_210 T_FPReg_76 T_FPReg_76 T_FPReg_76 |
    C_fsubS_212 T_FPReg_76 T_FPReg_76 T_FPReg_76 |
    C_fmulS_214 T_FPReg_76 T_FPReg_76 T_FPReg_76 |
    C_fdivS_216 T_FPReg_76 T_FPReg_76 T_FPReg_76 |
    C_fnegS_218 T_FPReg_76 T_FPReg_76 |
    C_fcvtDS_220 T_FPReg_76 T_FPReg_76
-- Once.Arith.Backend.RiscV.Syntax.ArithInstr
d_ArithInstr_222 = ()
data T_ArithInstr_222
  = C_intI_224 T_IntInstr_158 | C_fpI_226 T_FPInstr_196
-- Once.Arith.Backend.RiscV.Syntax.ArithProgram
d_ArithProgram_228 :: ()
d_ArithProgram_228 = erased
