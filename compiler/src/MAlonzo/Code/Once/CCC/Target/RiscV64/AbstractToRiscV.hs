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
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax
import qualified MAlonzo.Code.Once.Target.Symbol

-- Once.CCC.Target.RiscV64.AbstractToRiscV.slot-to-disp
d_slot'45'to'45'disp_10 :: Integer -> Integer
d_slot'45'to'45'disp_10 v0
  = coe
      mulInt (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_108)
-- Once.CCC.Target.RiscV64.AbstractToRiscV.compile-abstract
d_compile'45'abstract_14 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_1882 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_54]
d_compile'45'abstract_14 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_1884
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_70
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_1886
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_70
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_1888
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_70
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a1_22)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_1890
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_70
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a1_22))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_1892
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_56
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44)
                (coe (0 :: Integer)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_1894
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_56
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44)
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_108))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_1896 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_56
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_fp_18)
                (coe d_slot'45'to'45'disp_10 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_1898 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_58
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_fp_18)
                (coe d_slot'45'to'45'disp_10 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_1900
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_58
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44)
                (coe (0 :: Integer)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_1902
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_58
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44)
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_108))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_1904 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_64
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_fp_18)
                (coe d_slot'45'to'45'disp_10 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_1906 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_56
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_fp_18)
                (coe d_slot'45'to'45'disp_10 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_1908 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_64
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                (coe
                   MAlonzo.Code.Data.Integer.Base.d_'45'__260
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_110 (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_1910 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_64
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_110 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_1912 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_1914 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_64
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16)
                (coe
                   MAlonzo.Code.Data.Integer.Base.d_'45'__260
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_108)))
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
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_70
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
                               MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_110 (coe v1))))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_1916
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_70
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
                         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_108))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_1918
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_56
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_s1_36)
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_108))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_jalr_78
                   (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ra_14)
                   (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44)
                   (coe (0 :: Integer)))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_1920 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_1922 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_58
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_fp_18)
                (coe d_slot'45'to'45'disp_10 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_1924 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_56
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_fp_18)
                (coe d_slot'45'to'45'disp_10 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_1926 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_1932 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call'45'sym_86
                (coe
                   MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol_8
                   (coe MAlonzo.Code.Once.CCC.SigOp.Info.d_name_290 (coe v3))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_1936 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_unimp_90)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_1938 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_unimp_90)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_1940
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_70
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_s1_36)
                (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_1942 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_unimp_90)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_1944 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_unimp_90)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_1946 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.AbstractToRiscV.compile-trace
d_compile'45'trace_52 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_1882] ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_54]
d_compile'45'trace_52 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_compile'45'abstract_14 (coe v1))
             (coe d_compile'45'trace_52 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
