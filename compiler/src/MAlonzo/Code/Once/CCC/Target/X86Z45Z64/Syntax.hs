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

module MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base

-- Once.CCC.Target.X86-64.Syntax.Reg
d_Reg_10 = ()
data T_Reg_10
  = C_rax_12 | C_rbx_14 | C_rcx_16 | C_rdx_18 | C_rsi_20 | C_rdi_22 |
    C_rbp_24 | C_rsp_26 | C_r8_28 | C_r9_30 | C_r10_32 | C_r11_34 |
    C_r12_36 | C_r13_38 | C_r14_40 | C_r15_42
-- Once.CCC.Target.X86-64.Syntax.Mem
d_Mem_44 = ()
data T_Mem_44
  = C_base_46 T_Reg_10 | C_base'43'disp_48 T_Reg_10 Integer |
    C_rip'43'disp_50 Integer
-- Once.CCC.Target.X86-64.Syntax.Operand
d_Operand_52 = ()
data T_Operand_52
  = C_reg_54 T_Reg_10 | C_mem_56 T_Mem_44 | C_imm_58 Integer
-- Once.CCC.Target.X86-64.Syntax.Instr
d_Instr_60 = ()
data T_Instr_60
  = C_mov_62 T_Operand_52 T_Operand_52 | C_lea_64 T_Reg_10 T_Mem_44 |
    C_add_66 T_Operand_52 T_Operand_52 |
    C_sub_68 T_Operand_52 T_Operand_52 |
    C_cmp_70 T_Operand_52 T_Operand_52 |
    C_test_72 T_Operand_52 T_Operand_52 | C_jmp_74 Integer |
    C_je_76 Integer | C_jne_78 Integer | C_call_80 T_Operand_52 |
    C_ret_82 | C_push_84 T_Operand_52 | C_pop_86 T_Reg_10 | C_nop_88 |
    C_ud2_90 | C_syscall_92 | C_label_94 Integer
-- Once.CCC.Target.X86-64.Syntax.Program
d_Program_96 :: ()
d_Program_96 = erased
-- Once.CCC.Target.X86-64.Syntax.Function
d_Function_98 = ()
data T_Function_98 = C_mkfun_108 Integer [T_Instr_60]
-- Once.CCC.Target.X86-64.Syntax.Function.name
d_name_104 :: T_Function_98 -> Integer
d_name_104 v0
  = case coe v0 of
      C_mkfun_108 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Syntax.Function.body
d_body_106 :: T_Function_98 -> [T_Instr_60]
d_body_106 v0
  = case coe v0 of
      C_mkfun_108 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Syntax.slot-size
d_slot'45'size_110 :: Integer
d_slot'45'size_110 = coe (8 :: Integer)
-- Once.CCC.Target.X86-64.Syntax.slots
d_slots_112 :: Integer -> Integer
d_slots_112 v0 = coe mulInt (coe v0) (coe d_slot'45'size_110)
-- Once.CCC.Target.X86-64.Syntax.sub-rsp-consumed
d_sub'45'rsp'45'consumed_116 :: T_Reg_10 -> T_Operand_52 -> Integer
d_sub'45'rsp'45'consumed_116 v0 v1
  = case coe v0 of
      C_rax_12 -> coe (0 :: Integer)
      C_rbx_14 -> coe (0 :: Integer)
      C_rcx_16 -> coe (0 :: Integer)
      C_rdx_18 -> coe (0 :: Integer)
      C_rsi_20 -> coe (0 :: Integer)
      C_rdi_22 -> coe (0 :: Integer)
      C_rbp_24 -> coe (0 :: Integer)
      C_rsp_26
        -> case coe v1 of
             C_reg_54 v2 -> coe (0 :: Integer)
             C_mem_56 v2 -> coe (0 :: Integer)
             C_imm_58 v2
               -> coe
                    MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v2)
                    (coe d_slot'45'size_110)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_r8_28 -> coe (0 :: Integer)
      C_r9_30 -> coe (0 :: Integer)
      C_r10_32 -> coe (0 :: Integer)
      C_r11_34 -> coe (0 :: Integer)
      C_r12_36 -> coe (0 :: Integer)
      C_r13_38 -> coe (0 :: Integer)
      C_r14_40 -> coe (0 :: Integer)
      C_r15_42 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Syntax.instr-consumed-slots
d_instr'45'consumed'45'slots_124 :: T_Instr_60 -> Integer
d_instr'45'consumed'45'slots_124 v0
  = case coe v0 of
      C_mov_62 v1 v2 -> coe (0 :: Integer)
      C_lea_64 v1 v2 -> coe (0 :: Integer)
      C_add_66 v1 v2 -> coe (0 :: Integer)
      C_sub_68 v1 v2
        -> case coe v1 of
             C_reg_54 v3 -> coe d_sub'45'rsp'45'consumed_116 (coe v3) (coe v2)
             C_mem_56 v3 -> coe (0 :: Integer)
             C_imm_58 v3 -> coe (0 :: Integer)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_cmp_70 v1 v2 -> coe (0 :: Integer)
      C_test_72 v1 v2 -> coe (0 :: Integer)
      C_jmp_74 v1 -> coe (0 :: Integer)
      C_je_76 v1 -> coe (0 :: Integer)
      C_jne_78 v1 -> coe (0 :: Integer)
      C_call_80 v1 -> coe (1 :: Integer)
      C_ret_82 -> coe (0 :: Integer)
      C_push_84 v1 -> coe (1 :: Integer)
      C_pop_86 v1 -> coe (0 :: Integer)
      C_nop_88 -> coe (0 :: Integer)
      C_ud2_90 -> coe (0 :: Integer)
      C_syscall_92 -> coe (0 :: Integer)
      C_label_94 v1 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Syntax.instrs-consumed-slots
d_instrs'45'consumed'45'slots_130 :: [T_Instr_60] -> Integer
d_instrs'45'consumed'45'slots_130
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         (\ v0 -> addInt (coe d_instr'45'consumed'45'slots_124 (coe v0))))
      (coe (0 :: Integer))
-- Once.CCC.Target.X86-64.Syntax.fstOffset
d_fstOffset_136 :: Integer
d_fstOffset_136 = coe (0 :: Integer)
-- Once.CCC.Target.X86-64.Syntax.sndOffset
d_sndOffset_138 :: Integer
d_sndOffset_138 = coe d_slot'45'size_110
-- Once.CCC.Target.X86-64.Syntax.tagOffset
d_tagOffset_140 :: Integer
d_tagOffset_140 = coe (0 :: Integer)
-- Once.CCC.Target.X86-64.Syntax.valueOffset
d_valueOffset_142 :: Integer
d_valueOffset_142 = coe d_slot'45'size_110
-- Once.CCC.Target.X86-64.Syntax.inlTag
d_inlTag_144 :: Integer
d_inlTag_144 = coe (0 :: Integer)
-- Once.CCC.Target.X86-64.Syntax.inrTag
d_inrTag_146 :: Integer
d_inrTag_146 = coe (1 :: Integer)
