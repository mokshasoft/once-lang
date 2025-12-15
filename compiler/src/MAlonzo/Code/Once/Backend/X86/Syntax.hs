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
  = C_base_44 T_Reg_8 | C_base'43'disp_46 T_Reg_8 Integer
-- Once.Backend.X86.Syntax.Operand
d_Operand_48 = ()
data T_Operand_48
  = C_reg_50 T_Reg_8 | C_mem_52 T_Mem_42 | C_imm_54 Integer
-- Once.Backend.X86.Syntax.Instr
d_Instr_56 = ()
data T_Instr_56
  = C_mov_58 T_Operand_48 T_Operand_48 | C_lea_60 T_Reg_8 T_Mem_42 |
    C_add_62 T_Operand_48 T_Operand_48 |
    C_sub_64 T_Operand_48 T_Operand_48 |
    C_cmp_66 T_Operand_48 T_Operand_48 |
    C_test_68 T_Operand_48 T_Operand_48 | C_jmp_70 Integer |
    C_je_72 Integer | C_jne_74 Integer | C_call_76 T_Operand_48 |
    C_ret_78 | C_push_80 T_Operand_48 | C_pop_82 T_Reg_8 | C_nop_84 |
    C_ud2_86 | C_label_88 Integer
-- Once.Backend.X86.Syntax.Program
d_Program_90 :: ()
d_Program_90 = erased
-- Once.Backend.X86.Syntax.Function
d_Function_92 = ()
data T_Function_92 = C_mkfun_102 Integer [T_Instr_56]
-- Once.Backend.X86.Syntax.Function.name
d_name_98 :: T_Function_92 -> Integer
d_name_98 v0
  = case coe v0 of
      C_mkfun_102 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.X86.Syntax.Function.body
d_body_100 :: T_Function_92 -> [T_Instr_56]
d_body_100 v0
  = case coe v0 of
      C_mkfun_102 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.X86.Syntax.fstOffset
d_fstOffset_104 :: Integer
d_fstOffset_104 = coe (0 :: Integer)
-- Once.Backend.X86.Syntax.sndOffset
d_sndOffset_106 :: Integer
d_sndOffset_106 = coe (8 :: Integer)
-- Once.Backend.X86.Syntax.tagOffset
d_tagOffset_108 :: Integer
d_tagOffset_108 = coe (0 :: Integer)
-- Once.Backend.X86.Syntax.valueOffset
d_valueOffset_110 :: Integer
d_valueOffset_110 = coe (8 :: Integer)
-- Once.Backend.X86.Syntax.inlTag
d_inlTag_112 :: Integer
d_inlTag_112 = coe (0 :: Integer)
-- Once.Backend.X86.Syntax.inrTag
d_inrTag_114 :: Integer
d_inrTag_114 = coe (1 :: Integer)
