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

module MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg

-- Once.CCC.Target.X86-32.Syntax.Mem
d_Mem_10 = ()
data T_Mem_10
  = C_base_12 MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 |
    C_base'43'disp_14 MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8
                      Integer |
    C_label'45'rel_16 Integer |
    C_abs'45'sym_18 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.CCC.Target.X86-32.Syntax.Operand
d_Operand_20 = ()
data T_Operand_20
  = C_reg_22 MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 |
    C_mem_24 T_Mem_10 | C_imm_26 Integer
-- Once.CCC.Target.X86-32.Syntax.Instr
d_Instr_28 = ()
data T_Instr_28
  = C_mov_30 T_Operand_20 T_Operand_20 |
    C_lea_32 MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8
             T_Mem_10 |
    C_push_34 T_Operand_20 |
    C_pop_36 MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 |
    C_add_38 T_Operand_20 T_Operand_20 |
    C_sub_40 T_Operand_20 T_Operand_20 |
    C_sbb_42 T_Operand_20 T_Operand_20 |
    C_cmp_44 T_Operand_20 T_Operand_20 |
    C_test_46 T_Operand_20 T_Operand_20 | C_jmp_48 T_Operand_20 |
    C_jne_50 MAlonzo.Code.Once.CCC.Label.T_Label_28 |
    C_je_52 MAlonzo.Code.Once.CCC.Label.T_Label_28 |
    C_call_54 T_Operand_20 |
    C_call'45'sym_56 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_call'45'l_58 MAlonzo.Code.Once.CCC.Label.T_Label_28 | C_ret_60 |
    C_nop_62 | C_ud2_64 |
    C_label_66 MAlonzo.Code.Once.CCC.Label.T_Label_28 |
    C_mov'45'code_68 MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8
                     MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_jmp'45'l_70 MAlonzo.Code.Once.CCC.Label.T_Label_28
-- Once.CCC.Target.X86-32.Syntax.Program
d_Program_72 :: ()
d_Program_72 = erased
-- Once.CCC.Target.X86-32.Syntax.slot-size
d_slot'45'size_74 :: Integer
d_slot'45'size_74 = coe (4 :: Integer)
-- Once.CCC.Target.X86-32.Syntax.slots
d_slots_76 :: Integer -> Integer
d_slots_76 v0 = coe mulInt (coe v0) (coe d_slot'45'size_74)
