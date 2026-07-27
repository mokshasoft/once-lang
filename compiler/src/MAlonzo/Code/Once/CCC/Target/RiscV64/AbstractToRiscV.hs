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
import qualified MAlonzo.Code.Once.Target.RiscV64.PhysReg
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Target.RiscV64.AbstractToRiscV.slot-to-disp
d_slot'45'to'45'disp_10 :: Integer -> Integer
d_slot'45'to'45'disp_10 v0
  = coe
      mulInt (coe v0)
      (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_66)
-- Once.CCC.Target.RiscV64.AbstractToRiscV.compile-abstract
d_compile'45'abstract_14 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10]
d_compile'45'abstract_14 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2162
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_28
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2164
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_28
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2166
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_28
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a1_20)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2168
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_28
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a1_20))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2170
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                (coe (0 :: Integer)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2172
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_66))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2174 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe d_slot'45'to'45'disp_10 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2176 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe d_slot'45'to'45'disp_10 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2178
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                (coe (0 :: Integer)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2180
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_66))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2182 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe d_slot'45'to'45'disp_10 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2184 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe d_slot'45'to'45'disp_10 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2186 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe
                   MAlonzo.Code.Data.Integer.Base.d_'45'__260
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_68 (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2188 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_68 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2190 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2192 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe
                   MAlonzo.Code.Data.Integer.Base.d_'45'__260
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_66)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_fp_16)
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                   (coe (0 :: Integer)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_28
                      (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_fp_16)
                      (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20
                         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                         (coe
                            MAlonzo.Code.Data.Integer.Base.d_'45'__260
                            (coe
                               MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_68 (coe v1))))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2194
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_28
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_fp_16))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_fp_16)
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                   (coe (0 :: Integer)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20
                      (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                      (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_fp_16)
                      (coe
                         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_66))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2196
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s1_34)
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_66))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_jalr_36
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_ra_12)
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                   (coe (0 :: Integer)))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2198 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2200 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe d_slot'45'to'45'disp_10 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2202 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe d_slot'45'to'45'disp_10 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2204 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2210 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call'45'sym_44
                (coe
                   MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_52
                   (coe MAlonzo.Code.Once.SigOp.Info.d_name_174 (coe v3))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2214 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_fits'45'int_198
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_22
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18) (coe v3))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.Type.C_fits'45'float_200
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_unimp_48)
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2216 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_lla_26
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18) (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2218
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_28
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s1_34)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2220 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_22
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18) (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2222 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_unimp_48)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2224 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_28
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s2_36))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s2_36)
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s2_36)
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_68 (coe v1)))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2226 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_unimp_48)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2228 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_508
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_22
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s3_38)
                       (coe (1 :: Integer)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_510
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_22
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s3_38)
                       (coe (0 :: Integer)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_512
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s3_38)
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s3_38)
                       (coe
                          MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe (1 :: Integer))))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_514
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_28
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s3_38)
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s4_40))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_516
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_22
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s4_40)
                       (coe (0 :: Integer)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_518
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s4_40)
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s4_40)
                       (coe (1 :: Integer)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2230 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2152 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_50 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2154 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_j_38 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2156 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_beq_30
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s3_38)
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_zero_10) (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2158 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                       (coe (0 :: Integer)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_beq_30
                          (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                          (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_zero_10) (coe v2))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2232 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe d_slot'45'to'45'disp_10 (coe v1)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_28
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s3_38))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_add_16
                      (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                      (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                      (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_add_16
                         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_add_16
                            (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                            (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                            (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_add_16
                               (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                               (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                               (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44))
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.AbstractToRiscV.compile-trace-cnt
d_compile'45'trace'45'cnt_72 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
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
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2222 v5 v6
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
                                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                                (coe (0 :: Integer)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_beq_30
                                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_zero_10)
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
                                            MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_j_38
                                            (coe addInt (coe (1 :: Integer)) (coe v0)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_50
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
                                               MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_50
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
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2226 v5
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
                                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_50 (coe v0))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_beq_30
                                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s3_38)
                                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_zero_10)
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
                                         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_j_38
                                         (coe v0))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_50
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
