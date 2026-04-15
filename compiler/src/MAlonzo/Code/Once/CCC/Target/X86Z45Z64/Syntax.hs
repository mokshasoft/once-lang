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
    C_ud2_90 | C_label_92 Integer
-- Once.CCC.Target.X86-64.Syntax.Program
d_Program_94 :: ()
d_Program_94 = erased
-- Once.CCC.Target.X86-64.Syntax.Function
d_Function_96 = ()
data T_Function_96 = C_mkfun_106 Integer [T_Instr_60]
-- Once.CCC.Target.X86-64.Syntax.Function.name
d_name_102 :: T_Function_96 -> Integer
d_name_102 v0
  = case coe v0 of
      C_mkfun_106 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Syntax.Function.body
d_body_104 :: T_Function_96 -> [T_Instr_60]
d_body_104 v0
  = case coe v0 of
      C_mkfun_106 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Syntax.slot-size
d_slot'45'size_108 :: Integer
d_slot'45'size_108 = coe (8 :: Integer)
-- Once.CCC.Target.X86-64.Syntax.slots
d_slots_110 :: Integer -> Integer
d_slots_110 v0 = coe mulInt (coe v0) (coe d_slot'45'size_108)
-- Once.CCC.Target.X86-64.Syntax.instr-consumed-slots
d_instr'45'consumed'45'slots_114 :: T_Instr_60 -> Integer
d_instr'45'consumed'45'slots_114 v0
  = let v1 = 0 :: Integer in
    coe
      (case coe v0 of
         C_sub_68 v2 v3
           -> case coe v3 of
                C_imm_58 v4
                  -> case coe v2 of
                       C_reg_54 v5
                         -> case coe v5 of
                              C_rsp_26
                                -> coe
                                     MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v4)
                                     (coe d_slot'45'size_108)
                              _ -> coe (0 :: Integer)
                       _ -> coe (0 :: Integer)
                _ -> coe v1
         C_call_80 v2 -> coe (1 :: Integer)
         C_push_84 v2 -> coe (1 :: Integer)
         _ -> coe v1)
-- Once.CCC.Target.X86-64.Syntax.instrs-consumed-slots
d_instrs'45'consumed'45'slots_136 :: [T_Instr_60] -> Integer
d_instrs'45'consumed'45'slots_136
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         (\ v0 -> addInt (coe d_instr'45'consumed'45'slots_114 (coe v0))))
      (coe (0 :: Integer))
-- Once.CCC.Target.X86-64.Syntax.fstOffset
d_fstOffset_142 :: Integer
d_fstOffset_142 = coe (0 :: Integer)
-- Once.CCC.Target.X86-64.Syntax.sndOffset
d_sndOffset_144 :: Integer
d_sndOffset_144 = coe d_slot'45'size_108
-- Once.CCC.Target.X86-64.Syntax.tagOffset
d_tagOffset_146 :: Integer
d_tagOffset_146 = coe (0 :: Integer)
-- Once.CCC.Target.X86-64.Syntax.valueOffset
d_valueOffset_148 :: Integer
d_valueOffset_148 = coe d_slot'45'size_108
-- Once.CCC.Target.X86-64.Syntax.inlTag
d_inlTag_150 :: Integer
d_inlTag_150 = coe (0 :: Integer)
-- Once.CCC.Target.X86-64.Syntax.inrTag
d_inrTag_152 :: Integer
d_inrTag_152 = coe (1 :: Integer)
