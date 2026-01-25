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
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base

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
-- Once.Backend.X86.Syntax.slot-size
d_slot'45'size_106 :: Integer
d_slot'45'size_106 = coe (8 :: Integer)
-- Once.Backend.X86.Syntax.slots
d_slots_108 :: Integer -> Integer
d_slots_108 v0 = coe mulInt (coe v0) (coe d_slot'45'size_106)
-- Once.Backend.X86.Syntax.instr-consumed-slots
d_instr'45'consumed'45'slots_112 :: T_Instr_58 -> Integer
d_instr'45'consumed'45'slots_112 v0
  = let v1 = 0 :: Integer in
    coe
      (case coe v0 of
         C_sub_66 v2 v3
           -> case coe v3 of
                C_imm_56 v4
                  -> case coe v2 of
                       C_reg_52 v5
                         -> case coe v5 of
                              C_rsp_24
                                -> coe
                                     MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v4)
                                     (coe d_slot'45'size_106)
                              _ -> coe (0 :: Integer)
                       _ -> coe (0 :: Integer)
                _ -> coe v1
         C_call_78 v2 -> coe (1 :: Integer)
         C_push_82 v2 -> coe (1 :: Integer)
         _ -> coe v1)
-- Once.Backend.X86.Syntax.instrs-consumed-slots
d_instrs'45'consumed'45'slots_134 :: [T_Instr_58] -> Integer
d_instrs'45'consumed'45'slots_134
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         (\ v0 -> addInt (coe d_instr'45'consumed'45'slots_112 (coe v0))))
      (coe (0 :: Integer))
-- Once.Backend.X86.Syntax.fstOffset
d_fstOffset_140 :: Integer
d_fstOffset_140 = coe (0 :: Integer)
-- Once.Backend.X86.Syntax.sndOffset
d_sndOffset_142 :: Integer
d_sndOffset_142 = coe d_slot'45'size_106
-- Once.Backend.X86.Syntax.tagOffset
d_tagOffset_144 :: Integer
d_tagOffset_144 = coe (0 :: Integer)
-- Once.Backend.X86.Syntax.valueOffset
d_valueOffset_146 :: Integer
d_valueOffset_146 = coe d_slot'45'size_106
-- Once.Backend.X86.Syntax.inlTag
d_inlTag_148 :: Integer
d_inlTag_148 = coe (0 :: Integer)
-- Once.Backend.X86.Syntax.inrTag
d_inrTag_150 :: Integer
d_inrTag_150 = coe (1 :: Integer)
