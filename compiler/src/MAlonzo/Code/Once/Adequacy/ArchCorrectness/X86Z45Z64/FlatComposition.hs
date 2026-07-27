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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160
d_fetch_46 ~v0 = du_fetch_46
du_fetch_46 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160
du_fetch_46 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_148
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.fl-go
d_fl'45'go_56 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer -> Integer -> Maybe Integer
d_fl'45'go_56 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'go_100 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.fl-label-match
d_fl'45'label'45'match_58 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer -> Integer -> Maybe Integer
d_fl'45'label'45'match_58 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'label'45'match_102
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.x86-len
d_x86'45'len_104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160 ->
  Integer
d_x86'45'len_104 ~v0 v1 = du_x86'45'len_104 v1
du_x86'45'len_104 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160 ->
  Integer
du_x86'45'len_104 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_length_268
      (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_compile'45'abstract_14
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.x86-off
d_x86'45'off_108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer -> Integer
d_x86'45'off_108 ~v0 v1 v2 = du_x86'45'off_108 v1 v2
du_x86'45'off_108 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer -> Integer
du_x86'45'off_108 v0 v1
  = case coe v1 of
      0 -> coe (0 :: Integer)
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                [] -> coe (0 :: Integer)
                (:) v3 v4
                  -> coe
                       addInt (coe du_x86'45'off_108 (coe v4) (coe v2))
                       (coe du_x86'45'len_104 (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.has-label
d_has'45'label_116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] -> Bool
d_has'45'label_116 ~v0 v1 = du_has'45'label_116 v1
du_has'45'label_116 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] -> Bool
du_has'45'label_116 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> let v3 = coe du_has'45'label_116 (coe v2) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_64 v4
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-label-go-skip
d_find'45'label'45'go'45'skip_128 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_6 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'go'45'skip_128 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.HeadView
d_HeadView_316 a0 a1 = ()
data T_HeadView_316
  = C_hv'45'clabel_328 Integer | C_hv'45'plain_336
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.reg-op-no-label
d_reg'45'op'45'no'45'label_340 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_506 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reg'45'op'45'no'45'label_340 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.const-no-label
d_const'45'no'45'label_348 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_const'45'no'45'label_348 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.headView
d_headView_356 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160 ->
  T_HeadView_316
d_headView_356 ~v0 v1 = du_headView_356 v1
du_headView_356 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160 ->
  T_HeadView_316
du_headView_356 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2162
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2164
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2166
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2168
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2170
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2172
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2174 v1
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2176 v1
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2178
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2180
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2182 v1
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2184 v1
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2186 v1
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2188 v1
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2190 v1
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2192 v1
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2194
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2196
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2198 v1
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2200 v1
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2202 v1
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2204 v1
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2210 v1 v2 v3
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2214 v1 v2 v3
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2216 v1
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2218
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2220 v1
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2222 v1 v2
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2224 v1
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2226 v1
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2228 v1
        -> coe C_hv'45'plain_336
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2230 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2152 v2
               -> coe C_hv'45'clabel_328 v2
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2154 v2
               -> coe C_hv'45'plain_336
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2156 v2
               -> coe C_hv'45'plain_336
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2158 v2
               -> coe C_hv'45'plain_336
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2232 v1
        -> coe C_hv'45'plain_336
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.just-inj
d_just'45'inj_598 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_598 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-label-pres
d_find'45'label'45'pres_612 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'label'45'pres_612 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7
  = du_find'45'label'45'pres_612 v1 v2 v6
du_find'45'label'45'pres_612 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'label'45'pres_612 v0 v1 v2
  = case coe v0 of
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
               -> case coe v7 of
                    C_hv'45'clabel_328 v9
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
                                              du_find'45'label'45'pres_612 (coe v4) (coe v1)
                                              (coe v8))))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    C_hv'45'plain_336
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              addInt (coe (1 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe du_find'45'label'45'pres_612 (coe v4) (coe v1) (coe v8))))
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.acc≡j
d_acc'8801'j_700 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer ->
  Integer ->
  Integer ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
   Integer ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_acc'8801'j_700 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.comp1
d_comp1_704 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer ->
  Integer ->
  Integer ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
   Integer ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comp1_704 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.all-headView
d_all'45'headView_754 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'45'headView_754 ~v0 v1 = du_all'45'headView_754 v1
du_all'45'headView_754 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_all'45'headView_754 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe du_headView_356 (coe v1))
             (coe du_all'45'headView_754 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-label-corr
d_find'45'label'45'corr_768 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'corr_768 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.drop-len-++
d_drop'45'len'45''43''43'_810 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'len'45''43''43'_810 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.drop-[]
d_drop'45''91''93'_824 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45''91''93'_824 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.drop-+
d_drop'45''43'_836 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  Integer ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45''43'_836 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.drop-compile
d_drop'45'compile_858 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'compile_858 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-drop
d_fetch'45'drop_874 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'drop_874 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-at-offset
d_fetch'45'at'45'offset_894 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'at'45'offset_894 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.x86-off-suc
d_x86'45'off'45'suc_908 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x86'45'off'45'suc_908 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.drop-fetch
d_drop'45'fetch_936 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'fetch_936 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-head
d_fetch'45'block'45'head_962 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'head_962 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-2nd
d_fetch'45'block'45'2nd_980 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'2nd_980 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-3rd
d_fetch'45'block'45'3rd_1000 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'3rd_1000 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-4th
d_fetch'45'block'45'4th_1020 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'4th_1020 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-5th
d_fetch'45'block'45'5th_1040 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'5th_1040 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-6th
d_fetch'45'block'45'6th_1060 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'6th_1060 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-label-none-go
d_find'45'label'45'none'45'go_1082 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'none'45'go_1082 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.absurd
d_absurd_1162 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
   Integer ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_absurd_1162 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-label-none-corr
d_find'45'label'45'none'45'corr_1200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2160] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'none'45'corr_1200 = erased
