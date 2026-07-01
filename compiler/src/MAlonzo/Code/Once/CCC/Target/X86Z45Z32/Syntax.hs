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

-- Once.CCC.Target.X86-32.Syntax.Reg
d_Reg_10 = ()
data T_Reg_10
  = C_eax_12 | C_ebx_14 | C_ecx_16 | C_edx_18 | C_esi_20 | C_edi_22 |
    C_ebp_24 | C_esp_26
-- Once.CCC.Target.X86-32.Syntax.Mem
d_Mem_28 = ()
data T_Mem_28
  = C_base_30 T_Reg_10 | C_base'43'disp_32 T_Reg_10 Integer |
    C_label'45'rel_34 Integer
-- Once.CCC.Target.X86-32.Syntax.Operand
d_Operand_36 = ()
data T_Operand_36
  = C_reg_38 T_Reg_10 | C_mem_40 T_Mem_28 | C_imm_42 Integer
-- Once.CCC.Target.X86-32.Syntax.Instr
d_Instr_44 = ()
data T_Instr_44
  = C_mov_46 T_Operand_36 T_Operand_36 | C_lea_48 T_Reg_10 T_Mem_28 |
    C_push_50 T_Operand_36 | C_pop_52 T_Reg_10 |
    C_add_54 T_Operand_36 T_Operand_36 |
    C_sub_56 T_Operand_36 T_Operand_36 |
    C_cmp_58 T_Operand_36 T_Operand_36 |
    C_test_60 T_Operand_36 T_Operand_36 | C_jmp_62 T_Operand_36 |
    C_jne_64 Integer | C_je_66 Integer | C_call_68 T_Operand_36 |
    C_call'45'sym_70 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_ret_72 | C_nop_74 | C_ud2_76 | C_label_78 Integer |
    C_mov'45'code_80 T_Reg_10 Integer | C_jmp'45'l_82 Integer
-- Once.CCC.Target.X86-32.Syntax.Program
d_Program_84 :: ()
d_Program_84 = erased
-- Once.CCC.Target.X86-32.Syntax.slot-size
d_slot'45'size_86 :: Integer
d_slot'45'size_86 = coe (4 :: Integer)
-- Once.CCC.Target.X86-32.Syntax.slots
d_slots_88 :: Integer -> Integer
d_slots_88 v0 = coe mulInt (coe v0) (coe d_slot'45'size_86)
