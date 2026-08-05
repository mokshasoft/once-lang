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
    C_label'45'rel_16 Integer
-- Once.CCC.Target.X86-32.Syntax.Operand
d_Operand_18 = ()
data T_Operand_18
  = C_reg_20 MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 |
    C_mem_22 T_Mem_10 | C_imm_24 Integer
-- Once.CCC.Target.X86-32.Syntax.Instr
d_Instr_26 = ()
data T_Instr_26
  = C_mov_28 T_Operand_18 T_Operand_18 |
    C_lea_30 MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8
             T_Mem_10 |
    C_push_32 T_Operand_18 |
    C_pop_34 MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 |
    C_add_36 T_Operand_18 T_Operand_18 |
    C_sub_38 T_Operand_18 T_Operand_18 |
    C_cmp_40 T_Operand_18 T_Operand_18 |
    C_test_42 T_Operand_18 T_Operand_18 | C_jmp_44 T_Operand_18 |
    C_jne_46 MAlonzo.Code.Once.CCC.Label.T_Label_6 |
    C_je_48 MAlonzo.Code.Once.CCC.Label.T_Label_6 |
    C_call_50 T_Operand_18 |
    C_call'45'sym_52 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_ret_54 | C_nop_56 | C_ud2_58 |
    C_label_60 MAlonzo.Code.Once.CCC.Label.T_Label_6 |
    C_mov'45'code_62 MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8
                     Integer |
    C_jmp'45'l_64 MAlonzo.Code.Once.CCC.Label.T_Label_6
-- Once.CCC.Target.X86-32.Syntax.Program
d_Program_66 :: ()
d_Program_66 = erased
-- Once.CCC.Target.X86-32.Syntax.slot-size
d_slot'45'size_68 :: Integer
d_slot'45'size_68 = coe (4 :: Integer)
-- Once.CCC.Target.X86-32.Syntax.slots
d_slots_70 :: Integer -> Integer
d_slots_70 v0 = coe mulInt (coe v0) (coe d_slot'45'size_68)
