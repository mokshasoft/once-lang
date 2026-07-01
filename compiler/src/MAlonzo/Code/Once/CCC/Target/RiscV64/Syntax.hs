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

module MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base

-- Once.CCC.Target.RiscV64.Syntax.Reg
d_Reg_10 = ()
data T_Reg_10
  = C_zero_12 | C_ra_14 | C_sp_16 | C_fp_18 | C_a0_20 | C_a1_22 |
    C_a2_24 | C_a3_26 | C_a4_28 | C_a5_30 | C_a6_32 | C_a7_34 |
    C_s1_36 | C_s2_38 | C_s3_40 | C_s4_42 | C_t0_44 | C_t1_46 |
    C_t2_48 | C_t3_50 | C_t4_52
-- Once.CCC.Target.RiscV64.Syntax.Instr
d_Instr_54 = ()
data T_Instr_54
  = C_ld_56 T_Reg_10 T_Reg_10 Integer |
    C_sd_58 T_Reg_10 T_Reg_10 Integer |
    C_add_60 T_Reg_10 T_Reg_10 T_Reg_10 |
    C_sub_62 T_Reg_10 T_Reg_10 T_Reg_10 |
    C_addi_64 T_Reg_10 T_Reg_10 Integer | C_li_66 T_Reg_10 Integer |
    C_auipc_68 T_Reg_10 Integer | C_lla_70 T_Reg_10 Integer |
    C_mv_72 T_Reg_10 T_Reg_10 | C_beq_74 T_Reg_10 T_Reg_10 Integer |
    C_bne_76 T_Reg_10 T_Reg_10 Integer | C_jal_78 T_Reg_10 Integer |
    C_jalr_80 T_Reg_10 T_Reg_10 Integer | C_j_82 Integer | C_ret_84 |
    C_call_86 Integer |
    C_call'45'sym_88 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_nop_90 | C_unimp_92 | C_label_94 Integer
-- Once.CCC.Target.RiscV64.Syntax.Program
d_Program_96 :: ()
d_Program_96 = erased
-- Once.CCC.Target.RiscV64.Syntax.Function
d_Function_98 = ()
data T_Function_98 = C_mkfun_108 Integer [T_Instr_54]
-- Once.CCC.Target.RiscV64.Syntax.Function.name
d_name_104 :: T_Function_98 -> Integer
d_name_104 v0
  = case coe v0 of
      C_mkfun_108 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Syntax.Function.body
d_body_106 :: T_Function_98 -> [T_Instr_54]
d_body_106 v0
  = case coe v0 of
      C_mkfun_108 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Syntax.slot-size
d_slot'45'size_110 :: Integer
d_slot'45'size_110 = coe (8 :: Integer)
-- Once.CCC.Target.RiscV64.Syntax.slots
d_slots_112 :: Integer -> Integer
d_slots_112 v0 = coe mulInt (coe v0) (coe d_slot'45'size_110)
-- Once.CCC.Target.RiscV64.Syntax.instr-consumed-slots
d_instr'45'consumed'45'slots_116 :: T_Instr_54 -> Integer
d_instr'45'consumed'45'slots_116 v0
  = coe seq (coe v0) (coe (0 :: Integer))
-- Once.CCC.Target.RiscV64.Syntax.program-consumed-slots
d_program'45'consumed'45'slots_118 :: [T_Instr_54] -> Integer
d_program'45'consumed'45'slots_118 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216 (coe addInt)
      (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe d_instr'45'consumed'45'slots_116) (coe v0))
