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

module MAlonzo.Code.Once.Backend.RiscV64.Syntax where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

-- Once.Backend.RiscV64.Syntax.Reg
d_Reg_8 = ()
data T_Reg_8
  = C_zero_10 | C_ra_12 | C_sp_14 | C_gp_16 | C_tp_18 | C_t0_20 |
    C_t1_22 | C_t2_24 | C_s0_26 | C_s1_28 | C_a0_30 | C_a1_32 |
    C_a2_34 | C_a3_36 | C_a4_38 | C_a5_40 | C_a6_42 | C_a7_44 |
    C_s2_46 | C_s3_48 | C_s4_50 | C_s5_52 | C_s6_54 | C_s7_56 |
    C_s8_58 | C_s9_60 | C_s10_62 | C_s11_64 | C_t3_66 | C_t4_68 |
    C_t5_70 | C_t6_72
-- Once.Backend.RiscV64.Syntax.Mem
d_Mem_74 = ()
data T_Mem_74 = C__'91'_'93'_84 T_Reg_8 Integer
-- Once.Backend.RiscV64.Syntax.Mem.base
d_base_80 :: T_Mem_74 -> T_Reg_8
d_base_80 v0
  = case coe v0 of
      C__'91'_'93'_84 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.RiscV64.Syntax.Mem.offset
d_offset_82 :: T_Mem_74 -> Integer
d_offset_82 v0
  = case coe v0 of
      C__'91'_'93'_84 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.RiscV64.Syntax.Instr
d_Instr_86 = ()
data T_Instr_86
  = C_add_88 T_Reg_8 T_Reg_8 T_Reg_8 |
    C_sub_90 T_Reg_8 T_Reg_8 T_Reg_8 |
    C_and_92 T_Reg_8 T_Reg_8 T_Reg_8 |
    C_or_94 T_Reg_8 T_Reg_8 T_Reg_8 |
    C_xor_96 T_Reg_8 T_Reg_8 T_Reg_8 |
    C_sll_98 T_Reg_8 T_Reg_8 T_Reg_8 |
    C_srl_100 T_Reg_8 T_Reg_8 T_Reg_8 |
    C_sra_102 T_Reg_8 T_Reg_8 T_Reg_8 |
    C_slt_104 T_Reg_8 T_Reg_8 T_Reg_8 |
    C_sltu_106 T_Reg_8 T_Reg_8 T_Reg_8 |
    C_addi_108 T_Reg_8 T_Reg_8 Integer |
    C_andi_110 T_Reg_8 T_Reg_8 Integer |
    C_ori_112 T_Reg_8 T_Reg_8 Integer |
    C_xori_114 T_Reg_8 T_Reg_8 Integer |
    C_slti_116 T_Reg_8 T_Reg_8 Integer |
    C_sltiu_118 T_Reg_8 T_Reg_8 Integer |
    C_slli_120 T_Reg_8 T_Reg_8 Integer |
    C_srli_122 T_Reg_8 T_Reg_8 Integer |
    C_srai_124 T_Reg_8 T_Reg_8 Integer |
    C_ld_126 T_Reg_8 Integer T_Reg_8 |
    C_lw_128 T_Reg_8 Integer T_Reg_8 |
    C_lwu_130 T_Reg_8 Integer T_Reg_8 |
    C_lh_132 T_Reg_8 Integer T_Reg_8 |
    C_lhu_134 T_Reg_8 Integer T_Reg_8 |
    C_lb_136 T_Reg_8 Integer T_Reg_8 |
    C_lbu_138 T_Reg_8 Integer T_Reg_8 |
    C_sd_140 T_Reg_8 Integer T_Reg_8 |
    C_sw_142 T_Reg_8 Integer T_Reg_8 |
    C_sh_144 T_Reg_8 Integer T_Reg_8 |
    C_sb_146 T_Reg_8 Integer T_Reg_8 |
    C_beq_148 T_Reg_8 T_Reg_8 Integer |
    C_bne_150 T_Reg_8 T_Reg_8 Integer |
    C_blt_152 T_Reg_8 T_Reg_8 Integer |
    C_bge_154 T_Reg_8 T_Reg_8 Integer |
    C_bltu_156 T_Reg_8 T_Reg_8 Integer |
    C_bgeu_158 T_Reg_8 T_Reg_8 Integer | C_lui_160 T_Reg_8 Integer |
    C_auipc_162 T_Reg_8 Integer | C_jal_164 T_Reg_8 Integer |
    C_jalr_166 T_Reg_8 T_Reg_8 Integer | C_li_168 T_Reg_8 Integer |
    C_mv_170 T_Reg_8 T_Reg_8 | C_j_172 Integer | C_call_174 Integer |
    C_ret_176 | C_nop_178 | C_ebreak_180 | C_label_182 Integer
-- Once.Backend.RiscV64.Syntax.Program
d_Program_184 :: ()
d_Program_184 = erased
-- Once.Backend.RiscV64.Syntax.Function
d_Function_186 = ()
data T_Function_186 = C_mkfun_196 Integer [T_Instr_86]
-- Once.Backend.RiscV64.Syntax.Function.name
d_name_192 :: T_Function_186 -> Integer
d_name_192 v0
  = case coe v0 of
      C_mkfun_196 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.RiscV64.Syntax.Function.body
d_body_194 :: T_Function_186 -> [T_Instr_86]
d_body_194 v0
  = case coe v0 of
      C_mkfun_196 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.RiscV64.Syntax.fstOffset
d_fstOffset_198 :: Integer
d_fstOffset_198 = coe (0 :: Integer)
-- Once.Backend.RiscV64.Syntax.sndOffset
d_sndOffset_200 :: Integer
d_sndOffset_200 = coe (8 :: Integer)
-- Once.Backend.RiscV64.Syntax.tagOffset
d_tagOffset_202 :: Integer
d_tagOffset_202 = coe (0 :: Integer)
-- Once.Backend.RiscV64.Syntax.valueOffset
d_valueOffset_204 :: Integer
d_valueOffset_204 = coe (8 :: Integer)
-- Once.Backend.RiscV64.Syntax.inlTag
d_inlTag_206 :: Integer
d_inlTag_206 = coe (0 :: Integer)
-- Once.Backend.RiscV64.Syntax.inrTag
d_inrTag_208 :: Integer
d_inrTag_208 = coe (1 :: Integer)
-- Once.Backend.RiscV64.Syntax.pairSize
d_pairSize_210 :: Integer
d_pairSize_210 = coe (16 :: Integer)
-- Once.Backend.RiscV64.Syntax.sumSize
d_sumSize_212 :: Integer
d_sumSize_212 = coe (16 :: Integer)
-- Once.Backend.RiscV64.Syntax.closureSize
d_closureSize_214 :: Integer
d_closureSize_214 = coe (16 :: Integer)
