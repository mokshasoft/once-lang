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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatComposition where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.is-label?
d_is'45'label'63'_12 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28 -> Bool
d_is'45'label'63'_12 ~v0 v1 = du_is'45'label'63'_12 v1
du_is'45'label'63'_12 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28 -> Bool
du_is'45'label'63'_12 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_30 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_lea_32 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_34 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_36 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_cmp_38 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_test_40 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jmp_42 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_je_44 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jne_46 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call_48 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call'45'sym_50 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ret_52
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_push_54 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_pop_56 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_nop_58
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_60
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_syscall_62
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_64 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.skip-law
d_skip'45'law_22 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_skip'45'law_22 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.label-hit
d_label'45'hit_140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_label'45'hit_140 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.label-miss
d_label'45'miss_164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_label'45'miss_164 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.HeadView
d_HeadView_182 a0 a1 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.has-label
d_has'45'label_184 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] -> Bool
d_has'45'label_184 ~v0 = du_has'45'label_184
du_has'45'label_184 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] -> Bool
du_has'45'label_184
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.du_has'45'label_30
      (coe du_is'45'label'63'_12)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.reg-op-no-label
d_reg'45'op'45'no'45'label_202 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reg'45'op'45'no'45'label_202 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.const-no-label
d_const'45'no'45'label_210 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_192 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_const'45'no'45'label_210 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.headView
d_headView_218 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.T_HeadView_50
d_headView_218 ~v0 v1 = du_headView_218 v1
du_headView_218 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.T_HeadView_50
du_headView_218 v0
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
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_36
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_22
                             (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_26
                             (coe
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_82
                                (coe v3))))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2216 v2
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2288 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.all-headView
d_all'45'headView_700 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'45'headView_700 ~v0 = du_all'45'headView_700
du_all'45'headView_700 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_all'45'headView_700
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_all'45'headView_942
      (coe du_headView_218)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.blk-len
d_blk'45'len_702 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer
d_blk'45'len_702 ~v0 = du_blk'45'len_702
du_blk'45'len_702 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer
du_blk'45'len_702
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_blk'45'len_124
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_compile'45'abstract_14)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.blk-off
d_blk'45'off_704 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer -> Integer
d_blk'45'off_704 ~v0 = du_blk'45'off_704
du_blk'45'off_704 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer -> Integer
du_blk'45'off_704
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_blk'45'off_128
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_compile'45'abstract_14)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.blk-off-suc
d_blk'45'off'45'suc_706 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_blk'45'off'45'suc_706 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.cons-step
d_cons'45'step_708 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cons'45'step_708 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.drop-+
d_drop'45''43'_710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  Integer ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45''43'_710 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.drop-[]
d_drop'45''91''93'_712 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45''91''93'_712 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.drop-compile
d_drop'45'compile_714 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'compile_714 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.drop-fetch
d_drop'45'fetch_716 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'fetch_716 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.drop-len-++
d_drop'45'len'45''43''43'_718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'len'45''43''43'_718 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.fetch-at-offset
d_fetch'45'at'45'offset_720 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'at'45'offset_720 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.fetch-block-2nd
d_fetch'45'block'45'2nd_722 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'2nd_722 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.fetch-block-3rd
d_fetch'45'block'45'3rd_724 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'3rd_724 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.fetch-block-4th
d_fetch'45'block'45'4th_726 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'4th_726 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.fetch-block-5th
d_fetch'45'block'45'5th_728 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'5th_728 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.fetch-block-6th
d_fetch'45'block'45'6th_730 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'6th_730 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.fetch-block-head
d_fetch'45'block'45'head_732 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'head_732 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.fetch-block-nth
d_fetch'45'block'45'nth_734 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'nth_734 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.fetch-drop
d_fetch'45'drop_736 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'drop_736 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.find-label-corr
d_find'45'label'45'corr_738 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'corr_738 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.find-label-go-skip
d_find'45'label'45'go'45'skip_740 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'go'45'skip_740 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.find-label-none-corr
d_find'45'label'45'none'45'corr_742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'none'45'corr_742 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.find-label-none-go
d_find'45'label'45'none'45'go_744 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'none'45'go_744 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.find-label-pres
d_find'45'label'45'pres_746 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'label'45'pres_746 ~v0 = du_find'45'label'45'pres_746
du_find'45'label'45'pres_746 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'label'45'pres_746 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_find'45'label'45'pres_788
      v0 v1 v5
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.find-thunk-corr
d_find'45'thunk'45'corr_748 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'thunk'45'corr_748 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.find-thunk-pres
d_find'45'thunk'45'pres_750 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'thunk'45'pres_750 ~v0 = du_find'45'thunk'45'pres_750
du_find'45'thunk'45'pres_750 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'thunk'45'pres_750 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_find'45'thunk'45'pres_616
      v0 v1 v5
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.hit-labelled
d_hit'45'labelled_752 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hit'45'labelled_752 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.just-inj
d_just'45'inj_754 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_754 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.skip-labelled
d_skip'45'labelled_756 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_skip'45'labelled_756 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.skip-plain
d_skip'45'plain_758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_skip'45'plain_758 = erased
