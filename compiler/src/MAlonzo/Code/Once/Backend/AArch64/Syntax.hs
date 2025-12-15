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

module MAlonzo.Code.Once.Backend.AArch64.Syntax where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

-- Once.Backend.AArch64.Syntax.Reg
d_Reg_8 = ()
data T_Reg_8
  = C_x0_10 | C_x1_12 | C_x2_14 | C_x3_16 | C_x4_18 | C_x5_20 |
    C_x6_22 | C_x7_24 | C_x8_26 | C_x9_28 | C_x10_30 | C_x11_32 |
    C_x12_34 | C_x13_36 | C_x14_38 | C_x15_40 | C_x16_42 | C_x17_44 |
    C_x18_46 | C_x19_48 | C_x20_50 | C_x21_52 | C_x22_54 | C_x23_56 |
    C_x24_58 | C_x25_60 | C_x26_62 | C_x27_64 | C_x28_66 | C_x29_68 |
    C_x30_70
-- Once.Backend.AArch64.Syntax.Mem
d_Mem_72 = ()
data T_Mem_72
  = C_base_74 T_Reg_8 | C_base'43'imm_76 T_Reg_8 Integer |
    C_sp'43'imm_78 Integer
-- Once.Backend.AArch64.Syntax.Operand
d_Operand_80 = ()
data T_Operand_80
  = C_reg_82 T_Reg_8 | C_mem_84 T_Mem_72 | C_imm_86 Integer
-- Once.Backend.AArch64.Syntax.Instr
d_Instr_88 = ()
data T_Instr_88
  = C_mov_90 T_Reg_8 T_Operand_80 | C_ldr_92 T_Reg_8 T_Mem_72 |
    C_str_94 T_Reg_8 T_Mem_72 | C_ldp_96 T_Reg_8 T_Reg_8 T_Mem_72 |
    C_stp_98 T_Reg_8 T_Reg_8 T_Mem_72 |
    C_add_100 T_Reg_8 T_Reg_8 T_Operand_80 |
    C_sub_102 T_Reg_8 T_Reg_8 T_Operand_80 |
    C_cmp_104 T_Reg_8 T_Operand_80 | C_b_106 Integer |
    C_b'45'eq_108 Integer | C_b'45'ne_110 Integer | C_bl_112 Integer |
    C_blr_114 T_Reg_8 | C_ret_116 | C_sub'45'sp_118 Integer |
    C_add'45'sp_120 Integer | C_mov'45'from'45'sp_122 T_Reg_8 |
    C_nop_124 | C_brk_126 Integer | C_str'45'zr_128 T_Mem_72 |
    C_label_130 Integer
-- Once.Backend.AArch64.Syntax.Program
d_Program_132 :: ()
d_Program_132 = erased
-- Once.Backend.AArch64.Syntax.Function
d_Function_134 = ()
data T_Function_134 = C_mkfun_144 Integer [T_Instr_88]
-- Once.Backend.AArch64.Syntax.Function.name
d_name_140 :: T_Function_134 -> Integer
d_name_140 v0
  = case coe v0 of
      C_mkfun_144 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.AArch64.Syntax.Function.body
d_body_142 :: T_Function_134 -> [T_Instr_88]
d_body_142 v0
  = case coe v0 of
      C_mkfun_144 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.AArch64.Syntax.fstOffset
d_fstOffset_146 :: Integer
d_fstOffset_146 = coe (0 :: Integer)
-- Once.Backend.AArch64.Syntax.sndOffset
d_sndOffset_148 :: Integer
d_sndOffset_148 = coe (8 :: Integer)
-- Once.Backend.AArch64.Syntax.tagOffset
d_tagOffset_150 :: Integer
d_tagOffset_150 = coe (0 :: Integer)
-- Once.Backend.AArch64.Syntax.valueOffset
d_valueOffset_152 :: Integer
d_valueOffset_152 = coe (8 :: Integer)
-- Once.Backend.AArch64.Syntax.inlTag
d_inlTag_154 :: Integer
d_inlTag_154 = coe (0 :: Integer)
-- Once.Backend.AArch64.Syntax.inrTag
d_inrTag_156 :: Integer
d_inrTag_156 = coe (1 :: Integer)
-- Once.Backend.AArch64.Syntax.pairFrameSize
d_pairFrameSize_158 :: Integer
d_pairFrameSize_158 = coe (16 :: Integer)
-- Once.Backend.AArch64.Syntax.sumFrameSize
d_sumFrameSize_160 :: Integer
d_sumFrameSize_160 = coe (16 :: Integer)
-- Once.Backend.AArch64.Syntax.closureFrameSize
d_closureFrameSize_162 :: Integer
d_closureFrameSize_162 = coe (16 :: Integer)
