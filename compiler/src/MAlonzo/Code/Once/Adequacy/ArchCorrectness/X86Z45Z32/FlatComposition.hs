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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.FlatComposition where

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
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.AbstractToX86Z45Z32
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax
import qualified MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition.is-label?
d_is'45'label'63'_12 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26 -> Bool
d_is'45'label'63'_12 ~v0 v1 = du_is'45'label'63'_12 v1
du_is'45'label'63'_12 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26 -> Bool
du_is'45'label'63'_12 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov_28 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_lea_30 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_push_32 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_pop_34 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_add_36 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_sub_38 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_cmp_40 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_test_42 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jmp_44 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jne_46 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_je_48 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call_50 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call'45'sym_52 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ret_54
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_nop_56
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_ud2_58
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_label_60 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_mov'45'code_62 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_jmp'45'l_64 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition.skip-law
d_skip'45'law_22 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_skip'45'law_22 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition.label-hit
d_label'45'hit_146 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_label'45'hit_146 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition.label-miss
d_label'45'miss_170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_label'45'miss_170 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.HeadView
d_HeadView_188 a0 a1 = ()
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.has-label
d_has'45'label_190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] -> Bool
d_has'45'label_190 ~v0 = du_has'45'label_190
du_has'45'label_190 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] -> Bool
du_has'45'label_190
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.du_has'45'label_30
      (coe du_is'45'label'63'_12)
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition.reg-op-no-label
d_reg'45'op'45'no'45'label_208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reg'45'op'45'no'45'label_208 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition.const-no-label
d_const'45'no'45'label_216 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_const'45'no'45'label_216 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition.headView
d_headView_224 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.T_HeadView_50
d_headView_224 ~v0 v1 = du_headView_224 v1
du_headView_224 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.T_HeadView_50
du_headView_224 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2208
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2210
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2212
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2214
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2216 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2218 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2220
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2222
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2224 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2226 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2228 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2230 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2232 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2234 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2236
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2238
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2240 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2242 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2244 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2246 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2252 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2256 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2258 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2260
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2262 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2264 v1 v2
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2266 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2268 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2270 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2272 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2194 v2
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'clabel_68
                    v2
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2196 v2
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2198 v2
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2200 v2
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2202 v2 v3
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'otherlabel_100
                    v2
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_sub_38
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_reg_20
                             (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_imm_24
                             (coe
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slots_70
                                (coe v3))))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2204 v2
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2274 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.C_hv'45'plain_82
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.all-headView
d_all'45'headView_706 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'45'headView_706 ~v0 = du_all'45'headView_706
du_all'45'headView_706 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_all'45'headView_706
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_all'45'headView_942
      (coe du_headView_224)
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.blk-len
d_blk'45'len_708 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206 ->
  Integer
d_blk'45'len_708 ~v0 = du_blk'45'len_708
du_blk'45'len_708 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206 ->
  Integer
du_blk'45'len_708
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_blk'45'len_124
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.AbstractToX86Z45Z32.d_compile'45'abstract_14)
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.blk-off
d_blk'45'off_710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer -> Integer
d_blk'45'off_710 ~v0 = du_blk'45'off_710
du_blk'45'off_710 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer -> Integer
du_blk'45'off_710
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_blk'45'off_128
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.AbstractToX86Z45Z32.d_compile'45'abstract_14)
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.blk-off-suc
d_blk'45'off'45'suc_712 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_blk'45'off'45'suc_712 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.cons-step
d_cons'45'step_714 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cons'45'step_714 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.drop-+
d_drop'45''43'_716 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  Integer ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45''43'_716 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.drop-[]
d_drop'45''91''93'_718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45''91''93'_718 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.drop-compile
d_drop'45'compile_720 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'compile_720 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.drop-fetch
d_drop'45'fetch_722 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'fetch_722 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.drop-len-++
d_drop'45'len'45''43''43'_724 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'len'45''43''43'_724 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.fetch-at-offset
d_fetch'45'at'45'offset_726 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'at'45'offset_726 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.fetch-block-2nd
d_fetch'45'block'45'2nd_728 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'2nd_728 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.fetch-block-3rd
d_fetch'45'block'45'3rd_730 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'3rd_730 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.fetch-block-4th
d_fetch'45'block'45'4th_732 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'4th_732 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.fetch-block-5th
d_fetch'45'block'45'5th_734 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'5th_734 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.fetch-block-6th
d_fetch'45'block'45'6th_736 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'6th_736 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.fetch-block-head
d_fetch'45'block'45'head_738 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'head_738 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.fetch-block-nth
d_fetch'45'block'45'nth_740 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'nth_740 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.fetch-drop
d_fetch'45'drop_742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'drop_742 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.find-label-corr
d_find'45'label'45'corr_744 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'corr_744 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.find-label-go-skip
d_find'45'label'45'go'45'skip_746 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'go'45'skip_746 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.find-label-none-corr
d_find'45'label'45'none'45'corr_748 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'none'45'corr_748 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.find-label-none-go
d_find'45'label'45'none'45'go_750 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'none'45'go_750 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.find-label-pres
d_find'45'label'45'pres_752 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'label'45'pres_752 ~v0 = du_find'45'label'45'pres_752
du_find'45'label'45'pres_752 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'label'45'pres_752 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_find'45'label'45'pres_788
      v0 v1 v5
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.find-thunk-corr
d_find'45'thunk'45'corr_754 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'thunk'45'corr_754 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.find-thunk-pres
d_find'45'thunk'45'pres_756 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'thunk'45'pres_756 ~v0 = du_find'45'thunk'45'pres_756
du_find'45'thunk'45'pres_756 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'thunk'45'pres_756 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_find'45'thunk'45'pres_616
      v0 v1 v5
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.hit-labelled
d_hit'45'labelled_758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hit'45'labelled_758 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.just-inj
d_just'45'inj_760 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_760 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.skip-labelled
d_skip'45'labelled_762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_skip'45'labelled_762 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition._.skip-plain
d_skip'45'plain_764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_skip'45'plain_764 = erased
