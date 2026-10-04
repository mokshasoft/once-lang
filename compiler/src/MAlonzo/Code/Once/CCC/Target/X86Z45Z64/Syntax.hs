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
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg

-- Once.CCC.Target.X86-64.Syntax.Mem
d_Mem_10 = ()
data T_Mem_10
  = C_base_12 MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 |
    C_base'43'disp_14 MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8
                      Integer |
    C_rip'43'disp_16 Integer |
    C_rip'43'label_18 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_rip'43'sym_20 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.CCC.Target.X86-64.Syntax.Operand
d_Operand_22 = ()
data T_Operand_22
  = C_reg_24 MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 |
    C_mem_26 T_Mem_10 | C_imm_28 Integer
-- Once.CCC.Target.X86-64.Syntax.Instr
d_Instr_30 = ()
data T_Instr_30
  = C_mov_32 T_Operand_22 T_Operand_22 |
    C_lea_34 MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8
             T_Mem_10 |
    C_add_36 T_Operand_22 T_Operand_22 |
    C_sub_38 T_Operand_22 T_Operand_22 |
    C_sbb_40 T_Operand_22 T_Operand_22 |
    C_cmp_42 T_Operand_22 T_Operand_22 |
    C_test_44 T_Operand_22 T_Operand_22 |
    C_jmp_46 MAlonzo.Code.Once.CCC.Label.T_Label_28 |
    C_je_48 MAlonzo.Code.Once.CCC.Label.T_Label_28 |
    C_jne_50 MAlonzo.Code.Once.CCC.Label.T_Label_28 |
    C_call_52 T_Operand_22 |
    C_call'45'sym_54 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_call'45'l_56 MAlonzo.Code.Once.CCC.Label.T_Label_28 | C_ret_58 |
    C_push_60 T_Operand_22 |
    C_pop_62 MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 |
    C_nop_64 | C_ud2_66 | C_syscall_68 |
    C_label_70 MAlonzo.Code.Once.CCC.Label.T_Label_28
-- Once.CCC.Target.X86-64.Syntax.Program
d_Program_72 :: ()
d_Program_72 = erased
-- Once.CCC.Target.X86-64.Syntax.Function
d_Function_74 = ()
data T_Function_74 = C_mkfun_84 Integer [T_Instr_30]
-- Once.CCC.Target.X86-64.Syntax.Function.name
d_name_80 :: T_Function_74 -> Integer
d_name_80 v0
  = case coe v0 of
      C_mkfun_84 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Syntax.Function.body
d_body_82 :: T_Function_74 -> [T_Instr_30]
d_body_82 v0
  = case coe v0 of
      C_mkfun_84 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Syntax.slot-size
d_slot'45'size_86 :: Integer
d_slot'45'size_86 = coe (8 :: Integer)
-- Once.CCC.Target.X86-64.Syntax.slots
d_slots_88 :: Integer -> Integer
d_slots_88 v0 = coe mulInt (coe v0) (coe d_slot'45'size_86)
-- Once.CCC.Target.X86-64.Syntax.sub-rsp-consumed
d_sub'45'rsp'45'consumed_92 ::
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  T_Operand_22 -> Integer
d_sub'45'rsp'45'consumed_92 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rcx_14
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdx_16
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsi_18
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbp_22
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24
        -> case coe v1 of
             C_reg_24 v2 -> coe (0 :: Integer)
             C_mem_26 v2 -> coe (0 :: Integer)
             C_imm_28 v2
               -> coe
                    MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v2)
                    (coe d_slot'45'size_86)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r8_26
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r9_28
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r10_30
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r11_32
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r12_34
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r13_36
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r14_38
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r15_40
        -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Syntax.instr-consumed-slots
d_instr'45'consumed'45'slots_100 :: T_Instr_30 -> Integer
d_instr'45'consumed'45'slots_100 v0
  = case coe v0 of
      C_mov_32 v1 v2 -> coe (0 :: Integer)
      C_lea_34 v1 v2 -> coe (0 :: Integer)
      C_add_36 v1 v2 -> coe (0 :: Integer)
      C_sub_38 v1 v2
        -> case coe v1 of
             C_reg_24 v3 -> coe d_sub'45'rsp'45'consumed_92 (coe v3) (coe v2)
             C_mem_26 v3 -> coe (0 :: Integer)
             C_imm_28 v3 -> coe (0 :: Integer)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_sbb_40 v1 v2 -> coe (0 :: Integer)
      C_cmp_42 v1 v2 -> coe (0 :: Integer)
      C_test_44 v1 v2 -> coe (0 :: Integer)
      C_jmp_46 v1 -> coe (0 :: Integer)
      C_je_48 v1 -> coe (0 :: Integer)
      C_jne_50 v1 -> coe (0 :: Integer)
      C_call_52 v1 -> coe (1 :: Integer)
      C_call'45'sym_54 v1 -> coe (1 :: Integer)
      C_call'45'l_56 v1 -> coe (1 :: Integer)
      C_ret_58 -> coe (0 :: Integer)
      C_push_60 v1 -> coe (1 :: Integer)
      C_pop_62 v1 -> coe (0 :: Integer)
      C_nop_64 -> coe (0 :: Integer)
      C_ud2_66 -> coe (0 :: Integer)
      C_syscall_68 -> coe (0 :: Integer)
      C_label_70 v1 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Syntax.instrs-consumed-slots
d_instrs'45'consumed'45'slots_106 :: [T_Instr_30] -> Integer
d_instrs'45'consumed'45'slots_106
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         (\ v0 -> addInt (coe d_instr'45'consumed'45'slots_100 (coe v0))))
      (coe (0 :: Integer))
-- Once.CCC.Target.X86-64.Syntax.fstOffset
d_fstOffset_112 :: Integer
d_fstOffset_112 = coe (0 :: Integer)
-- Once.CCC.Target.X86-64.Syntax.sndOffset
d_sndOffset_114 :: Integer
d_sndOffset_114 = coe d_slot'45'size_86
-- Once.CCC.Target.X86-64.Syntax.tagOffset
d_tagOffset_116 :: Integer
d_tagOffset_116 = coe (0 :: Integer)
-- Once.CCC.Target.X86-64.Syntax.valueOffset
d_valueOffset_118 :: Integer
d_valueOffset_118 = coe d_slot'45'size_86
-- Once.CCC.Target.X86-64.Syntax.inlTag
d_inlTag_120 :: Integer
d_inlTag_120 = coe (0 :: Integer)
-- Once.CCC.Target.X86-64.Syntax.inrTag
d_inrTag_122 :: Integer
d_inrTag_122 = coe (1 :: Integer)
