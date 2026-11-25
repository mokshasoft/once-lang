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
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.Target.RiscV64.PhysReg

-- Once.CCC.Target.RiscV64.Syntax.Instr
d_Instr_10 = ()
data T_Instr_10
  = C_ld_12 MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
            MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 Integer |
    C_sd_14 MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
            MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 Integer |
    C_add_16 MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
             MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
             MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 |
    C_sub_18 MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
             MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
             MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 |
    C_sltu_20 MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
              MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
              MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 |
    C_addi_22 MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
              MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 Integer |
    C_li_24 MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 Integer |
    C_auipc_26 MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
               Integer |
    C_lla_28 MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
             MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_lla'45'sym_30 MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
                    MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_mv_32 MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
            MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 |
    C_beq_34 MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
             MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
             MAlonzo.Code.Once.CCC.Label.T_Label_28 |
    C_bne_36 MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
             MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
             MAlonzo.Code.Once.CCC.Label.T_Label_28 |
    C_bgeu'45'fwd_38 MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
                     MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 |
    C_local'45'1_40 |
    C_bgeu'45'fwd2_42 MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
                      MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 |
    C_local'45'2_44 |
    C_jal_46 MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
             MAlonzo.Code.Once.CCC.Label.T_Label_28 |
    C_jalr_48 MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
              MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 Integer |
    C_j_50 MAlonzo.Code.Once.CCC.Label.T_Label_28 | C_ret_52 |
    C_call_54 Integer |
    C_call'45'sym_56 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_nop_58 | C_unimp_60 |
    C_label_62 MAlonzo.Code.Once.CCC.Label.T_Label_28
-- Once.CCC.Target.RiscV64.Syntax.Program
d_Program_64 :: ()
d_Program_64 = erased
-- Once.CCC.Target.RiscV64.Syntax.Function
d_Function_66 = ()
data T_Function_66 = C_mkfun_76 Integer [T_Instr_10]
-- Once.CCC.Target.RiscV64.Syntax.Function.name
d_name_72 :: T_Function_66 -> Integer
d_name_72 v0
  = case coe v0 of
      C_mkfun_76 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Syntax.Function.body
d_body_74 :: T_Function_66 -> [T_Instr_10]
d_body_74 v0
  = case coe v0 of
      C_mkfun_76 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Syntax.slot-size
d_slot'45'size_78 :: Integer
d_slot'45'size_78 = coe (8 :: Integer)
-- Once.CCC.Target.RiscV64.Syntax.slots
d_slots_80 :: Integer -> Integer
d_slots_80 v0 = coe mulInt (coe v0) (coe d_slot'45'size_78)
-- Once.CCC.Target.RiscV64.Syntax.instr-consumed-slots
d_instr'45'consumed'45'slots_84 :: T_Instr_10 -> Integer
d_instr'45'consumed'45'slots_84 v0
  = coe seq (coe v0) (coe (0 :: Integer))
-- Once.CCC.Target.RiscV64.Syntax.program-consumed-slots
d_program'45'consumed'45'slots_86 :: [T_Instr_10] -> Integer
d_program'45'consumed'45'slots_86 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216 (coe addInt)
      (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe d_instr'45'consumed'45'slots_84) (coe v0))
