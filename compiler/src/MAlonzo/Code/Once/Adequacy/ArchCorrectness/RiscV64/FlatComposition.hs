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
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_22 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_auipc_24 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_lla_26 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_28 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_beq_30 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_bne_32 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_jal_34 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_jalr_36 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_j_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ret_40
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call_42 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call'45'sym_44 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_nop_46
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_unimp_48
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_50 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition.skip-law
d_skip'45'law_22 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_skip'45'law_22 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition.label-hit
d_label'45'hit_152 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_label'45'hit_152 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition.label-miss
d_label'45'miss_176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_label'45'miss_176 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.HeadView
d_HeadView_194 a0 a1 = ()
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.has-label
d_has'45'label_196 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] -> Bool
d_has'45'label_196 ~v0 = du_has'45'label_196
du_has'45'label_196 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] -> Bool
du_has'45'label_196
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.du_has'45'label_30
      (coe du_is'45'label'63'_12)
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition.reg-op-no-label
d_reg'45'op'45'no'45'label_214 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reg'45'op'45'no'45'label_214 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition.const-no-label
d_const'45'no'45'label_222 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_192 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_const'45'no'45'label_222 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition.headView
d_headView_230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.T_HeadView_50
d_headView_230 ~v0 v1 = du_headView_230 v1
du_headView_230 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.T_HeadView_50
du_headView_230 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2236 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2238 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2240 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2242 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2244 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2246 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2248
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2250
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2252 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2254 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2256 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2258 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2264 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2270 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2272 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2274
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2278 v1 v2
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2282 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206 v2
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'clabel_68
                    v2
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208 v2
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2210 v2
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2212 v2
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2214 v2 v3
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'otherlabel_100
                    v2
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20
                          (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                          (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                          (coe
                             MAlonzo.Code.Data.Integer.Base.d_'45'__260
                             (coe
                                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_68 (coe v3))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14
                             (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_ra_12)
                             (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                             (coe
                                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_68 (coe v3)))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2216 v2
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2288 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.all-headView
d_all'45'headView_712 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'45'headView_712 ~v0 = du_all'45'headView_712
du_all'45'headView_712 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_all'45'headView_712
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_all'45'headView_942
      (coe du_headView_230)
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.blk-len
d_blk'45'len_714 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer
d_blk'45'len_714 ~v0 = du_blk'45'len_714
du_blk'45'len_714 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer
du_blk'45'len_714
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_blk'45'len_124
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.AbstractToRiscV.d_compile'45'abstract_168)
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.blk-off
d_blk'45'off_716 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer -> Integer
d_blk'45'off_716 ~v0 = du_blk'45'off_716
du_blk'45'off_716 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer -> Integer
du_blk'45'off_716
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_blk'45'off_128
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.AbstractToRiscV.d_compile'45'abstract_168)
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.blk-off-suc
d_blk'45'off'45'suc_718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_blk'45'off'45'suc_718 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.cons-step
d_cons'45'step_720 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cons'45'step_720 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.drop-+
d_drop'45''43'_722 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  Integer ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45''43'_722 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.drop-[]
d_drop'45''91''93'_724 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45''91''93'_724 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.drop-compile
d_drop'45'compile_726 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'compile_726 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.drop-fetch
d_drop'45'fetch_728 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'fetch_728 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.drop-len-++
d_drop'45'len'45''43''43'_730 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'len'45''43''43'_730 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.fetch-at-offset
d_fetch'45'at'45'offset_732 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'at'45'offset_732 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.fetch-block-2nd
d_fetch'45'block'45'2nd_734 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'2nd_734 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.fetch-block-3rd
d_fetch'45'block'45'3rd_736 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'3rd_736 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.fetch-block-4th
d_fetch'45'block'45'4th_738 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'4th_738 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.fetch-block-5th
d_fetch'45'block'45'5th_740 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'5th_740 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.fetch-block-6th
d_fetch'45'block'45'6th_742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'6th_742 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.fetch-block-head
d_fetch'45'block'45'head_744 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'head_744 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.fetch-block-nth
d_fetch'45'block'45'nth_746 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'nth_746 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.fetch-drop
d_fetch'45'drop_748 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'drop_748 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.find-label-corr
d_find'45'label'45'corr_750 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'corr_750 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.find-label-go-skip
d_find'45'label'45'go'45'skip_752 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'go'45'skip_752 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.find-label-none-corr
d_find'45'label'45'none'45'corr_754 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'none'45'corr_754 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.find-label-none-go
d_find'45'label'45'none'45'go_756 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'none'45'go_756 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.find-label-pres
d_find'45'label'45'pres_758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'label'45'pres_758 ~v0 = du_find'45'label'45'pres_758
du_find'45'label'45'pres_758 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'label'45'pres_758 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_find'45'label'45'pres_788
      v0 v1 v5
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.find-thunk-corr
d_find'45'thunk'45'corr_760 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'thunk'45'corr_760 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.find-thunk-pres
d_find'45'thunk'45'pres_762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'thunk'45'pres_762 ~v0 = du_find'45'thunk'45'pres_762
du_find'45'thunk'45'pres_762 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'thunk'45'pres_762 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_find'45'thunk'45'pres_616
      v0 v1 v5
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.hit-labelled
d_hit'45'labelled_764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hit'45'labelled_764 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.just-inj
d_just'45'inj_766 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_766 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.skip-labelled
d_skip'45'labelled_768 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_skip'45'labelled_768 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition._.skip-plain
d_skip'45'plain_770 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_skip'45'plain_770 = erased
