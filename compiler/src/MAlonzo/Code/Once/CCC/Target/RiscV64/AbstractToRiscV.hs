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

module MAlonzo.Code.Once.CCC.Target.RiscV64.AbstractToRiscV where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Target.RiscV64.AbstractToRiscV.slot-to-disp
d_slot'45'to'45'disp_10 :: Integer -> Integer
d_slot'45'to'45'disp_10 v0
  = coe
      mulInt (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_110)
-- Once.CCC.Target.RiscV64.AbstractToRiscV.compile-abstract
d_compile'45'abstract_14 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_54]
d_compile'45'abstract_14 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2050
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_72
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2052
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_72
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2054
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_72
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a1_22)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2056
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_72
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a1_22))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2058
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_56
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44)
                (coe (0 :: Integer)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2060
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_56
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44)
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_110))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2062 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_56
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                (coe d_slot'45'to'45'disp_10 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2064 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_58
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                (coe d_slot'45'to'45'disp_10 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2066
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_58
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44)
                (coe (0 :: Integer)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2068
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_58
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44)
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_110))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2070 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_64
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                (coe d_slot'45'to'45'disp_10 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2072 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_56
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                (coe d_slot'45'to'45'disp_10 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2074 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_64
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                (coe
                   MAlonzo.Code.Data.Integer.Base.d_'45'__260
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_112 (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2076 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_64
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_112 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2078 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2080 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_64
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                (coe
                   MAlonzo.Code.Data.Integer.Base.d_'45'__260
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_110)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_58
                   (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_fp_18)
                   (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                   (coe (0 :: Integer)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_72
                      (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_fp_18)
                      (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_64
                         (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                         (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                         (coe
                            MAlonzo.Code.Data.Integer.Base.d_'45'__260
                            (coe
                               MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_112 (coe v1))))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2082
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_72
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_fp_18))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_56
                   (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_fp_18)
                   (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                   (coe (0 :: Integer)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_64
                      (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                      (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_fp_18)
                      (coe
                         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_110))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2084
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_56
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t1_46)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_s1_36)
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_110))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_jalr_80
                   (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ra_14)
                   (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t1_46)
                   (coe (0 :: Integer)))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2086 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2088 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_58
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                (coe d_slot'45'to'45'disp_10 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2090 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_56
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                (coe d_slot'45'to'45'disp_10 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2092 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2098 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call'45'sym_88
                (coe
                   MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_52
                   (coe MAlonzo.Code.Once.SigOp.Info.d_name_160 (coe v3))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2102 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_fits'45'int_198
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_66
                       (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20) (coe v3))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.Type.C_fits'45'float_200
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_unimp_92)
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2104 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_lla_70
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20) (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2106
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_72
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_s1_36)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2108 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_66
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20) (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2110 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_unimp_92)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2112 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_72
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_s2_38))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_64
                   (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_s2_38)
                   (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_s2_38)
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_112 (coe v1)))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2114 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_unimp_92)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2116 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_424
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_66
                       (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_s3_40)
                       (coe (1 :: Integer)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_426
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_66
                       (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_s3_40)
                       (coe (0 :: Integer)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_428
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_64
                       (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_s3_40)
                       (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_s3_40)
                       (coe
                          MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe (1 :: Integer))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_430
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_72
                       (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_s3_40)
                       (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_s4_42))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_input2'45'zero_432
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_66
                       (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_s4_42)
                       (coe (0 :: Integer)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_input2'45'inc_434
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_64
                       (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_s4_42)
                       (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_s4_42)
                       (coe (1 :: Integer)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2118 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2040 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_94 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2042 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_j_82 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2044 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_beq_74
                       (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_s3_40)
                       (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_zero_12)
                       (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2046 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_56
                       (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t1_46)
                       (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44)
                       (coe (0 :: Integer)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_beq_74
                          (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t1_46)
                          (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_zero_12)
                          (coe v2))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2120 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_56
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                (coe d_slot'45'to'45'disp_10 (coe v1)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_72
                   (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t1_46)
                   (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_s3_40))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_add_60
                      (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t1_46)
                      (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t1_46)
                      (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t1_46))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_add_60
                         (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t1_46)
                         (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t1_46)
                         (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t1_46))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_add_60
                            (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t1_46)
                            (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t1_46)
                            (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t1_46))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_add_60
                               (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44)
                               (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44)
                               (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t1_46))
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.AbstractToRiscV.compile-trace-cnt
d_compile'45'trace'45'cnt_72 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compile'45'trace'45'cnt_72 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      (:) v2 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe d_compile'45'trace'45'cnt_72 (coe v0) (coe v3)))
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe d_compile'45'abstract_14 (coe v2))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                           (coe d_compile'45'trace'45'cnt_72 (coe v0) (coe v3)))) in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2110 v5 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_compile'45'trace'45'cnt_72
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   d_compile'45'trace'45'cnt_72
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         d_compile'45'trace'45'cnt_72
                                         (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v5)))
                                   (coe v6)))
                             (coe v3)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_56
                                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t1_46)
                                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44)
                                (coe (0 :: Integer)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_beq_74
                                   (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t1_46)
                                   (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_zero_12)
                                   (coe v0))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_compile'45'trace'45'cnt_72
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               d_compile'45'trace'45'cnt_72
                                               (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v5)))
                                         (coe v6)))
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_j_82
                                            (coe addInt (coe (1 :: Integer)) (coe v0)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_94
                                               (coe v0))
                                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                      (coe
                                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               d_compile'45'trace'45'cnt_72
                                               (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v5)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_94
                                               (coe addInt (coe (1 :: Integer)) (coe v0)))
                                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_compile'45'trace'45'cnt_72
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_compile'45'trace'45'cnt_72
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            d_compile'45'trace'45'cnt_72
                                            (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v5)))
                                      (coe v6)))
                                (coe v3))))
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2114 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_compile'45'trace'45'cnt_72
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   d_compile'45'trace'45'cnt_72
                                   (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v5)))
                             (coe v3)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_94 (coe v0))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_beq_74
                                   (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_s3_40)
                                   (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_zero_12)
                                   (coe addInt (coe (1 :: Integer)) (coe v0)))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_compile'45'trace'45'cnt_72
                                         (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v5)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_j_82
                                         (coe v0))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_94
                                            (coe addInt (coe (1 :: Integer)) (coe v0)))
                                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_compile'45'trace'45'cnt_72
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_compile'45'trace'45'cnt_72
                                      (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v5)))
                                (coe v3))))
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
