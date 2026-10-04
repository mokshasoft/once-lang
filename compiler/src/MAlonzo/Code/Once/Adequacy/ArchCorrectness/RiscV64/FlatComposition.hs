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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.AbstractToRiscV
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax
import qualified MAlonzo.Code.Once.Target.RiscV64.PhysReg
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition.is-label?
d_is'45'label'63'_12 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10 -> Bool
d_is'45'label'63'_12 ~v0 v1 = du_is'45'label'63'_12 v1
du_is'45'label'63'_12 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10 -> Bool
du_is'45'label'63'_12 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_add_16 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sub_18 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sltu_20 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_22 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_24 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_auipc_26 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_lla_28 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_lla'45'sym_30 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_32 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_beq_34 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_bne_36 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_jal_38 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_jalr_40 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_j_42 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ret_44
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call_46 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call'45'sym_48 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_nop_50
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_unimp_52
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_54 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition.skip-law
d_skip'45'law_22 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_skip'45'law_22 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition.label-hit
d_label'45'hit_164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_label'45'hit_164 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition.label-miss
d_label'45'miss_188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_label'45'miss_188 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.HeadView
d_HeadView_206 a0 a1 = ()
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.has-label
d_has'45'label_208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] -> Bool
d_has'45'label_208 ~v0 = du_has'45'label_208
du_has'45'label_208 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] -> Bool
du_has'45'label_208
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.du_has'45'label_30
      (coe du_is'45'label'63'_12)
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition.reg-op-no-label
d_reg'45'op'45'no'45'label_226 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reg'45'op'45'no'45'label_226 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition.const-no-label
d_const'45'no'45'label_234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_const'45'no'45'label_234 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition.headView
d_headView_242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.T_HeadView_50
d_headView_242 ~v0 v1 = du_headView_242 v1
du_headView_242 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.T_HeadView_50
du_headView_242 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2268 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2272 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2274 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2276 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2278 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2280
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2284 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2286 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2288 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2290 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2296 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2302 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2304 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2310 v1 v2
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2314 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228 v2
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'clabel_68
                    v2
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230 v2
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232 v2
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234 v2
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236 v2 v3
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'otherlabel_100
                    v2
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_22
                          (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                          (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                          (coe
                             MAlonzo.Code.Data.Integer.Base.d_'45'__260
                             (coe
                                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_72 (coe v3))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14
                             (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_ra_12)
                             (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                             (coe
                                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_72 (coe v3)))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2238 v2
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2240 v2
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2242 v2
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2320 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.all-headView
d_all'45'headView_752 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'45'headView_752 ~v0 = du_all'45'headView_752
du_all'45'headView_752 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_all'45'headView_752
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_all'45'headView_942
      (coe du_headView_242)
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.blk-len
d_blk'45'len_754 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  Integer
d_blk'45'len_754 ~v0 = du_blk'45'len_754
du_blk'45'len_754 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  Integer
du_blk'45'len_754
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_blk'45'len_124
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.AbstractToRiscV.d_compile'45'abstract_174)
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.blk-off
d_blk'45'off_756 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer -> Integer
d_blk'45'off_756 ~v0 = du_blk'45'off_756
du_blk'45'off_756 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer -> Integer
du_blk'45'off_756
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_blk'45'off_128
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.AbstractToRiscV.d_compile'45'abstract_174)
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.blk-off-suc
d_blk'45'off'45'suc_758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_blk'45'off'45'suc_758 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.cons-step
d_cons'45'step_760 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cons'45'step_760 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.drop-+
d_drop'45''43'_762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  Integer ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45''43'_762 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.drop-[]
d_drop'45''91''93'_764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45''91''93'_764 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.drop-compile
d_drop'45'compile_766 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'compile_766 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.drop-fetch
d_drop'45'fetch_768 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'fetch_768 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.drop-len-++
d_drop'45'len'45''43''43'_770 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'len'45''43''43'_770 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.fetch-at-offset
d_fetch'45'at'45'offset_772 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'at'45'offset_772 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.fetch-block-2nd
d_fetch'45'block'45'2nd_774 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'2nd_774 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.fetch-block-3rd
d_fetch'45'block'45'3rd_776 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'3rd_776 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.fetch-block-4th
d_fetch'45'block'45'4th_778 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'4th_778 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.fetch-block-5th
d_fetch'45'block'45'5th_780 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'5th_780 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.fetch-block-6th
d_fetch'45'block'45'6th_782 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'6th_782 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.fetch-block-head
d_fetch'45'block'45'head_784 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'head_784 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.fetch-block-nth
d_fetch'45'block'45'nth_786 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'nth_786 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.fetch-drop
d_fetch'45'drop_788 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'drop_788 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.find-label-corr
d_find'45'label'45'corr_790 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'corr_790 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.find-label-go-skip
d_find'45'label'45'go'45'skip_792 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'go'45'skip_792 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.find-label-none-corr
d_find'45'label'45'none'45'corr_794 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'none'45'corr_794 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.find-label-none-go
d_find'45'label'45'none'45'go_796 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'none'45'go_796 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.find-label-pres
d_find'45'label'45'pres_798 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'label'45'pres_798 ~v0 = du_find'45'label'45'pres_798
du_find'45'label'45'pres_798 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'label'45'pres_798 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_find'45'label'45'pres_788
      v0 v1 v5
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.find-thunk-corr
d_find'45'thunk'45'corr_800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'thunk'45'corr_800 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.find-thunk-pres
d_find'45'thunk'45'pres_802 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'thunk'45'pres_802 ~v0 = du_find'45'thunk'45'pres_802
du_find'45'thunk'45'pres_802 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'thunk'45'pres_802 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_find'45'thunk'45'pres_616
      v0 v1 v5
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.hit-labelled
d_hit'45'labelled_804 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hit'45'labelled_804 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.just-inj
d_just'45'inj_806 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_806 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.skip-labelled
d_skip'45'labelled_808 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_skip'45'labelled_808 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.skip-plain
d_skip'45'plain_810 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_skip'45'plain_810 = erased
