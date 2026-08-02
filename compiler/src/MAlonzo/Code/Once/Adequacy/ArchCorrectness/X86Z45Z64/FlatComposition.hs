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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.fetch
d_fetch_46 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238
d_fetch_46 ~v0 = du_fetch_46
du_fetch_46 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238
du_fetch_46 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_148
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.fl-go
d_fl'45'go_56 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer -> Integer -> Maybe Integer
d_fl'45'go_56 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'go_100 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.fl-label-match
d_fl'45'label'45'match_58 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer -> Integer -> Maybe Integer
d_fl'45'label'45'match_58 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'label'45'match_102
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.x86-len
d_x86'45'len_106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Integer
d_x86'45'len_106 ~v0 v1 = du_x86'45'len_106 v1
du_x86'45'len_106 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Integer
du_x86'45'len_106 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_length_268
      (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_compile'45'abstract_14
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.x86-off
d_x86'45'off_110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer -> Integer
d_x86'45'off_110 ~v0 v1 v2 = du_x86'45'off_110 v1 v2
du_x86'45'off_110 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer -> Integer
du_x86'45'off_110 v0 v1
  = case coe v1 of
      0 -> coe (0 :: Integer)
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                [] -> coe (0 :: Integer)
                (:) v3 v4
                  -> coe
                       addInt (coe du_x86'45'off_110 (coe v4) (coe v2))
                       (coe du_x86'45'len_106 (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.has-label
d_has'45'label_118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] -> Bool
d_has'45'label_118 ~v0 v1 = du_has'45'label_118 v1
du_has'45'label_118 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] -> Bool
du_has'45'label_118 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> let v3 = coe du_has'45'label_118 (coe v2) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_64 v4
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-label-go-skip
d_find'45'label'45'go'45'skip_130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_6 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'go'45'skip_130 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.HeadView
d_HeadView_318 a0 a1 = ()
data T_HeadView_318
  = C_hv'45'clabel_330 Integer | C_hv'45'plain_338
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.reg-op-no-label
d_reg'45'op'45'no'45'label_342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_506 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reg'45'op'45'no'45'label_342 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.const-no-label
d_const'45'no'45'label_350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_const'45'no'45'label_350 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.headView
d_headView_358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  T_HeadView_318
d_headView_358 ~v0 v1 = du_headView_358 v1
du_headView_358 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  T_HeadView_318
du_headView_358 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2244
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2246
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2248
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2250
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2252 v1
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2254 v1
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2256
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2258
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2260 v1
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2262 v1
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2264 v1
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2266 v1
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2268 v1
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2270 v1
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2272
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2274
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2276 v1
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2278 v1
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2280 v1
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2282 v1
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2288 v1 v2 v3
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2292 v1 v2 v3
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2294 v1
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2296
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2298 v1
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2300 v1 v2
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2302 v1
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2304 v1
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2306 v1
        -> coe C_hv'45'plain_338
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2308 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2230 v2
               -> coe C_hv'45'clabel_330 v2
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2232 v2
               -> coe C_hv'45'plain_338
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2234 v2
               -> coe C_hv'45'plain_338
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2236 v2
               -> coe C_hv'45'plain_338
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2310 v1
        -> coe C_hv'45'plain_338
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.just-inj
d_just'45'inj_600 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_600 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-label-pres
d_find'45'label'45'pres_614 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'label'45'pres_614 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7
  = du_find'45'label'45'pres_614 v1 v2 v6
du_find'45'label'45'pres_614 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'label'45'pres_614 v0 v1 v2
  = case coe v0 of
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
               -> case coe v7 of
                    C_hv'45'clabel_330 v9
                      -> let v12 = eqInt (coe v9) (coe v1) in
                         coe
                           (if coe v12
                              then coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe (0 :: Integer))
                                     (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
                              else coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        addInt (coe (1 :: Integer))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                           (coe
                                              du_find'45'label'45'pres_614 (coe v4) (coe v1)
                                              (coe v8))))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    C_hv'45'plain_338
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              addInt (coe (1 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe du_find'45'label'45'pres_614 (coe v4) (coe v1) (coe v8))))
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.acc≡j
d_acc'8801'j_702 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  Integer ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   Integer ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_acc'8801'j_702 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.comp1
d_comp1_706 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  Integer ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   Integer ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comp1_706 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.all-headView
d_all'45'headView_756 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'45'headView_756 ~v0 v1 = du_all'45'headView_756 v1
du_all'45'headView_756 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_all'45'headView_756 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe du_headView_358 (coe v1))
             (coe du_all'45'headView_756 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-label-corr
d_find'45'label'45'corr_770 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'corr_770 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.drop-len-++
d_drop'45'len'45''43''43'_812 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'len'45''43''43'_812 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.drop-[]
d_drop'45''91''93'_826 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45''91''93'_826 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.drop-+
d_drop'45''43'_838 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  Integer ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45''43'_838 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.drop-compile
d_drop'45'compile_860 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'compile_860 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-drop
d_fetch'45'drop_876 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'drop_876 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-at-offset
d_fetch'45'at'45'offset_896 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'at'45'offset_896 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.x86-off-suc
d_x86'45'off'45'suc_910 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x86'45'off'45'suc_910 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.drop-fetch
d_drop'45'fetch_938 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'fetch_938 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-head
d_fetch'45'block'45'head_964 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'head_964 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-2nd
d_fetch'45'block'45'2nd_982 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'2nd_982 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-3rd
d_fetch'45'block'45'3rd_1002 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'3rd_1002 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-4th
d_fetch'45'block'45'4th_1022 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'4th_1022 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-5th
d_fetch'45'block'45'5th_1042 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'5th_1042 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-6th
d_fetch'45'block'45'6th_1062 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'6th_1062 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-label-none-go
d_find'45'label'45'none'45'go_1084 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'none'45'go_1084 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.absurd
d_absurd_1164 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   Integer ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_absurd_1164 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-label-none-corr
d_find'45'label'45'none'45'corr_1202 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'none'45'corr_1202 = erased
