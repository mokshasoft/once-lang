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
    C_auipc_68 T_Reg_10 Integer | C_mv_70 T_Reg_10 T_Reg_10 |
    C_beq_72 T_Reg_10 T_Reg_10 Integer |
    C_bne_74 T_Reg_10 T_Reg_10 Integer | C_jal_76 T_Reg_10 Integer |
    C_jalr_78 T_Reg_10 T_Reg_10 Integer | C_j_80 Integer | C_ret_82 |
    C_call_84 Integer | C_nop_86 | C_unimp_88 | C_label_90 Integer
-- Once.CCC.Target.RiscV64.Syntax.Program
d_Program_92 :: ()
d_Program_92 = erased
-- Once.CCC.Target.RiscV64.Syntax.Function
d_Function_94 = ()
data T_Function_94 = C_mkfun_104 Integer [T_Instr_54]
-- Once.CCC.Target.RiscV64.Syntax.Function.name
d_name_100 :: T_Function_94 -> Integer
d_name_100 v0
  = case coe v0 of
      C_mkfun_104 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Syntax.Function.body
d_body_102 :: T_Function_94 -> [T_Instr_54]
d_body_102 v0
  = case coe v0 of
      C_mkfun_104 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Syntax.slot-size
d_slot'45'size_106 :: Integer
d_slot'45'size_106 = coe (8 :: Integer)
-- Once.CCC.Target.RiscV64.Syntax.slots
d_slots_108 :: Integer -> Integer
d_slots_108 v0 = coe mulInt (coe v0) (coe d_slot'45'size_106)
-- Once.CCC.Target.RiscV64.Syntax.instr-consumed-slots
d_instr'45'consumed'45'slots_112 :: T_Instr_54 -> Integer
d_instr'45'consumed'45'slots_112 v0
  = coe seq (coe v0) (coe (0 :: Integer))
-- Once.CCC.Target.RiscV64.Syntax.program-consumed-slots
d_program'45'consumed'45'slots_114 :: [T_Instr_54] -> Integer
d_program'45'consumed'45'slots_114 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216 (coe addInt)
      (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe d_instr'45'consumed'45'slots_112) (coe v0))
