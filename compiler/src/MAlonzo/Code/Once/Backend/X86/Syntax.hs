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

module MAlonzo.Code.Once.Backend.X86.Syntax where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

-- Once.Backend.X86.Syntax.Reg
d_Reg_8 = ()
data T_Reg_8
  = C_rax_10 | C_rbx_12 | C_rcx_14 | C_rdx_16 | C_rsi_18 | C_rdi_20 |
    C_rbp_22 | C_rsp_24 | C_r8_26 | C_r9_28 | C_r10_30 | C_r11_32 |
    C_r12_34 | C_r13_36 | C_r14_38 | C_r15_40
-- Once.Backend.X86.Syntax.Mem
d_Mem_42 = ()
data T_Mem_42
  = C_base_44 T_Reg_8 | C_base'43'disp_46 T_Reg_8 Integer |
    C_rip'43'disp_48 Integer
-- Once.Backend.X86.Syntax.Operand
d_Operand_50 = ()
data T_Operand_50
  = C_reg_52 T_Reg_8 | C_mem_54 T_Mem_42 | C_imm_56 Integer
-- Once.Backend.X86.Syntax.Instr
d_Instr_58 = ()
data T_Instr_58
  = C_mov_60 T_Operand_50 T_Operand_50 | C_lea_62 T_Reg_8 T_Mem_42 |
    C_add_64 T_Operand_50 T_Operand_50 |
    C_sub_66 T_Operand_50 T_Operand_50 |
    C_cmp_68 T_Operand_50 T_Operand_50 |
    C_test_70 T_Operand_50 T_Operand_50 | C_jmp_72 Integer |
    C_je_74 Integer | C_jne_76 Integer | C_call_78 T_Operand_50 |
    C_ret_80 | C_push_82 T_Operand_50 | C_pop_84 T_Reg_8 | C_nop_86 |
    C_ud2_88 | C_label_90 Integer
-- Once.Backend.X86.Syntax.Program
d_Program_92 :: ()
d_Program_92 = erased
-- Once.Backend.X86.Syntax.Function
d_Function_94 = ()
data T_Function_94 = C_mkfun_104 Integer [T_Instr_58]
-- Once.Backend.X86.Syntax.Function.name
d_name_100 :: T_Function_94 -> Integer
d_name_100 v0
  = case coe v0 of
      C_mkfun_104 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.X86.Syntax.Function.body
d_body_102 :: T_Function_94 -> [T_Instr_58]
d_body_102 v0
  = case coe v0 of
      C_mkfun_104 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.X86.Syntax.fstOffset
d_fstOffset_106 :: Integer
d_fstOffset_106 = coe (0 :: Integer)
-- Once.Backend.X86.Syntax.sndOffset
d_sndOffset_108 :: Integer
d_sndOffset_108 = coe (8 :: Integer)
-- Once.Backend.X86.Syntax.tagOffset
d_tagOffset_110 :: Integer
d_tagOffset_110 = coe (0 :: Integer)
-- Once.Backend.X86.Syntax.valueOffset
d_valueOffset_112 :: Integer
d_valueOffset_112 = coe (8 :: Integer)
-- Once.Backend.X86.Syntax.inlTag
d_inlTag_114 :: Integer
d_inlTag_114 = coe (0 :: Integer)
-- Once.Backend.X86.Syntax.inrTag
d_inrTag_116 :: Integer
d_inrTag_116 = coe (1 :: Integer)
