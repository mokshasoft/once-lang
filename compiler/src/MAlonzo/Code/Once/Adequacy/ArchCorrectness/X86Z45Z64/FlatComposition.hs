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
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.fetch
d_fetch_82 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286
d_fetch_82 ~v0 = du_fetch_82
du_fetch_82 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286
du_fetch_82 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_210
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.fl-go
d_fl'45'go_102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'go_102 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'go_122 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.fl-label-match
d_fl'45'label'45'match_108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'label'45'match_108 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'label'45'match_126
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.ft-go
d_ft'45'go_132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_ft'45'go_132 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'go_168 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.ft-match
d_ft'45'match_136 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_ft'45'match_136 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'match_172 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.x86-len
d_x86'45'len_202 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  Integer
d_x86'45'len_202 ~v0 v1 = du_x86'45'len_202 v1
du_x86'45'len_202 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  Integer
du_x86'45'len_202 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_length_268
      (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_compile'45'abstract_14
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.x86-off
d_x86'45'off_206 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer -> Integer
d_x86'45'off_206 ~v0 v1 v2 = du_x86'45'off_206 v1 v2
du_x86'45'off_206 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer -> Integer
du_x86'45'off_206 v0 v1
  = case coe v1 of
      0 -> coe (0 :: Integer)
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                [] -> coe (0 :: Integer)
                (:) v3 v4
                  -> coe
                       addInt (coe du_x86'45'off_206 (coe v4) (coe v2))
                       (coe du_x86'45'len_202 (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.has-label
d_has'45'label_214 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] -> Bool
d_has'45'label_214 ~v0 v1 = du_has'45'label_214 v1
du_has'45'label_214 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] -> Bool
du_has'45'label_214 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> let v3 = coe du_has'45'label_214 (coe v2) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_64 v4
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-label-go-skip
d_find'45'label'45'go'45'skip_226 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'go'45'skip_226 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-label-go-skip-other
d_find'45'label'45'go'45'skip'45'other_420 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'go'45'skip'45'other_420 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.HeadView
d_HeadView_438 a0 a1 = ()
data T_HeadView_438
  = C_hv'45'clabel_456 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_hv'45'plain_470 |
    C_hv'45'otherlabel_488 MAlonzo.Code.Once.CCC.Label.T_LabelId_6
                           [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28]
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.reg-op-no-label
d_reg'45'op'45'no'45'label_492 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_448 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reg'45'op'45'no'45'label_492 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.const-no-label
d_const'45'no'45'label_500 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_const'45'no'45'label_500 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.headView
d_headView_508 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  T_HeadView_438
d_headView_508 ~v0 v1 = du_headView_508 v1
du_headView_508 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  T_HeadView_438
du_headView_508 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2288
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2290
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2292
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2294
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2296
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2298
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2300 v1
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2302 v1
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2304
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2306
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2308 v1
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2310 v1
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2312 v1
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2314 v1
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2316 v1
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2318 v1
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2320
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2322
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2324 v1
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2326 v1
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2328 v1
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2330 v1
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2336 v1 v2 v3
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2340 v1 v2 v3
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2342 v1
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2344
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2346 v1
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2348 v1 v2
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2350 v1
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2352 v1
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2354 v1
        -> coe C_hv'45'plain_470
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2356 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2274 v2
               -> coe C_hv'45'clabel_456 v2
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2276 v2
               -> coe C_hv'45'plain_470
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2278 v2
               -> coe C_hv'45'plain_470
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2280 v2
               -> coe C_hv'45'plain_470
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2282 v2 v3
               -> coe
                    C_hv'45'otherlabel_488 v2
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
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2284 v2
               -> coe C_hv'45'plain_470
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2358 v1
        -> coe C_hv'45'plain_470
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-thunk-pres
d_find'45'thunk'45'pres_1004 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'thunk'45'pres_1004 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7
  = du_find'45'thunk'45'pres_1004 v1 v2 v6
du_find'45'thunk'45'pres_1004 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'thunk'45'pres_1004 v0 v1 v2
  = case coe v0 of
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
               -> case coe v7 of
                    C_hv'45'clabel_456 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              addInt (coe (1 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe du_find'45'thunk'45'pres_1004 (coe v4) (coe v1) (coe v8))))
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
                    C_hv'45'plain_470
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              addInt (coe (1 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe du_find'45'thunk'45'pres_1004 (coe v4) (coe v1) (coe v8))))
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
                    C_hv'45'otherlabel_488 v9 v10
                      -> let v15
                               = coe
                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                                   (let v15 = MAlonzo.Code.Once.CCC.Label.d_path_16 (coe v9) in
                                    coe
                                      (let v16 = MAlonzo.Code.Once.CCC.Label.d_idx_18 (coe v9) in
                                       coe
                                         (let v17
                                                = MAlonzo.Code.Once.CCC.Label.d_path_16 (coe v1) in
                                          coe
                                            (let v18
                                                   = MAlonzo.Code.Once.CCC.Label.d_idx_18
                                                       (coe v1) in
                                             coe
                                               (let v19
                                                      = coe
                                                          MAlonzo.Code.Data.List.Properties.du_'8801''45'dec_60
                                                          (coe
                                                             MAlonzo.Code.Data.String.Properties.d__'8799'__54)
                                                          (coe
                                                             MAlonzo.Code.Once.CanonicalName.d_parts_8
                                                             (coe
                                                                MAlonzo.Code.Once.CCC.Label.d_owner_14
                                                                (coe v9)))
                                                          (coe
                                                             MAlonzo.Code.Once.CanonicalName.d_parts_8
                                                             (coe
                                                                MAlonzo.Code.Once.CCC.Label.d_owner_14
                                                                (coe v1))) in
                                                coe
                                                  (case coe v19 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                       -> if coe v20
                                                            then let v22
                                                                       = seq
                                                                           (coe v21)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                              (coe v20)
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                 erased)) in
                                                                 coe
                                                                   (case coe v22 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                                        -> if coe v23
                                                                             then coe
                                                                                    seq (coe v24)
                                                                                    (let v25
                                                                                           = coe
                                                                                               MAlonzo.Code.Data.List.Properties.du_'8801''45'dec_60
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796)
                                                                                               (coe
                                                                                                  v15)
                                                                                               (coe
                                                                                                  v17) in
                                                                                     coe
                                                                                       (case coe
                                                                                               v25 of
                                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v26 v27
                                                                                            -> if coe
                                                                                                    v26
                                                                                                 then coe
                                                                                                        seq
                                                                                                        (coe
                                                                                                           v27)
                                                                                                        (let v28
                                                                                                               = coe
                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                   erased
                                                                                                                   (\ v28 ->
                                                                                                                      coe
                                                                                                                        MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                                                                                                        (coe
                                                                                                                           v16))
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                                                                                                      (coe
                                                                                                                         eqInt
                                                                                                                         (coe
                                                                                                                            v16)
                                                                                                                         (coe
                                                                                                                            v18))) in
                                                                                                         coe
                                                                                                           (case coe
                                                                                                                   v28 of
                                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v29 v30
                                                                                                                -> if coe
                                                                                                                        v29
                                                                                                                     then coe
                                                                                                                            seq
                                                                                                                            (coe
                                                                                                                               v30)
                                                                                                                            (coe
                                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                               (coe
                                                                                                                                  v29)
                                                                                                                               (coe
                                                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                                  erased))
                                                                                                                     else coe
                                                                                                                            seq
                                                                                                                            (coe
                                                                                                                               v30)
                                                                                                                            (coe
                                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                               (coe
                                                                                                                                  v29)
                                                                                                                               (coe
                                                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                 else coe
                                                                                                        seq
                                                                                                        (coe
                                                                                                           v27)
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                           (coe
                                                                                                              v26)
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                                             else coe
                                                                                    seq (coe v24)
                                                                                    (coe
                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                       (coe v23)
                                                                                       (coe
                                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                            else (let v22
                                                                        = seq
                                                                            (coe v21)
                                                                            (coe
                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                               (coe v20)
                                                                               (coe
                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                                                  coe
                                                                    (case coe v22 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                                         -> if coe v23
                                                                              then coe
                                                                                     seq (coe v24)
                                                                                     (let v25
                                                                                            = coe
                                                                                                MAlonzo.Code.Data.List.Properties.du_'8801''45'dec_60
                                                                                                (coe
                                                                                                   MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796)
                                                                                                (coe
                                                                                                   v15)
                                                                                                (coe
                                                                                                   v17) in
                                                                                      coe
                                                                                        (case coe
                                                                                                v25 of
                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v26 v27
                                                                                             -> if coe
                                                                                                     v26
                                                                                                  then coe
                                                                                                         seq
                                                                                                         (coe
                                                                                                            v27)
                                                                                                         (let v28
                                                                                                                = coe
                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                    erased
                                                                                                                    (\ v28 ->
                                                                                                                       coe
                                                                                                                         MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                                                                                                         (coe
                                                                                                                            v16))
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                                                                                                       (coe
                                                                                                                          eqInt
                                                                                                                          (coe
                                                                                                                             v16)
                                                                                                                          (coe
                                                                                                                             v18))) in
                                                                                                          coe
                                                                                                            (case coe
                                                                                                                    v28 of
                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v29 v30
                                                                                                                 -> if coe
                                                                                                                         v29
                                                                                                                      then coe
                                                                                                                             seq
                                                                                                                             (coe
                                                                                                                                v30)
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                (coe
                                                                                                                                   v29)
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                                   erased))
                                                                                                                      else coe
                                                                                                                             seq
                                                                                                                             (coe
                                                                                                                                v30)
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                (coe
                                                                                                                                   v29)
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                  else coe
                                                                                                         seq
                                                                                                         (coe
                                                                                                            v27)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                            (coe
                                                                                                               v26)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                                                              else coe
                                                                                     seq (coe v24)
                                                                                     (coe
                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                        (coe v23)
                                                                                        (coe
                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                     _ -> MAlonzo.RTE.mazUnreachableError)))))) in
                         coe
                           (if coe v15
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
                                              du_find'45'thunk'45'pres_1004 (coe v4) (coe v1)
                                              (coe v8))))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.jinj
d_jinj_1136 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_jinj_1136 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.acc≡j
d_acc'8801'j_1138 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_acc'8801'j_1138 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.comp1
d_comp1_1142 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comp1_1142 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.just-inj
d_just'45'inj_1198 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_1198 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-label-pres
d_find'45'label'45'pres_1212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'label'45'pres_1212 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7
  = du_find'45'label'45'pres_1212 v1 v2 v6
du_find'45'label'45'pres_1212 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'label'45'pres_1212 v0 v1 v2
  = case coe v0 of
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
               -> case coe v7 of
                    C_hv'45'clabel_456 v9
                      -> let v13
                               = coe
                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                                   (let v13 = MAlonzo.Code.Once.CCC.Label.d_path_16 (coe v9) in
                                    coe
                                      (let v14 = MAlonzo.Code.Once.CCC.Label.d_idx_18 (coe v9) in
                                       coe
                                         (let v15
                                                = MAlonzo.Code.Once.CCC.Label.d_path_16 (coe v1) in
                                          coe
                                            (let v16
                                                   = MAlonzo.Code.Once.CCC.Label.d_idx_18
                                                       (coe v1) in
                                             coe
                                               (let v17
                                                      = coe
                                                          MAlonzo.Code.Data.List.Properties.du_'8801''45'dec_60
                                                          (coe
                                                             MAlonzo.Code.Data.String.Properties.d__'8799'__54)
                                                          (coe
                                                             MAlonzo.Code.Once.CanonicalName.d_parts_8
                                                             (coe
                                                                MAlonzo.Code.Once.CCC.Label.d_owner_14
                                                                (coe v9)))
                                                          (coe
                                                             MAlonzo.Code.Once.CanonicalName.d_parts_8
                                                             (coe
                                                                MAlonzo.Code.Once.CCC.Label.d_owner_14
                                                                (coe v1))) in
                                                coe
                                                  (case coe v17 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                       -> if coe v18
                                                            then let v20
                                                                       = seq
                                                                           (coe v19)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                              (coe v18)
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                 erased)) in
                                                                 coe
                                                                   (case coe v20 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                        -> if coe v21
                                                                             then coe
                                                                                    seq (coe v22)
                                                                                    (let v23
                                                                                           = coe
                                                                                               MAlonzo.Code.Data.List.Properties.du_'8801''45'dec_60
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796)
                                                                                               (coe
                                                                                                  v13)
                                                                                               (coe
                                                                                                  v15) in
                                                                                     coe
                                                                                       (case coe
                                                                                               v23 of
                                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                                                            -> if coe
                                                                                                    v24
                                                                                                 then coe
                                                                                                        seq
                                                                                                        (coe
                                                                                                           v25)
                                                                                                        (let v26
                                                                                                               = coe
                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                   erased
                                                                                                                   (\ v26 ->
                                                                                                                      coe
                                                                                                                        MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                                                                                                        (coe
                                                                                                                           v14))
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                                                                                                      (coe
                                                                                                                         eqInt
                                                                                                                         (coe
                                                                                                                            v14)
                                                                                                                         (coe
                                                                                                                            v16))) in
                                                                                                         coe
                                                                                                           (case coe
                                                                                                                   v26 of
                                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v27 v28
                                                                                                                -> if coe
                                                                                                                        v27
                                                                                                                     then coe
                                                                                                                            seq
                                                                                                                            (coe
                                                                                                                               v28)
                                                                                                                            (coe
                                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                               (coe
                                                                                                                                  v27)
                                                                                                                               (coe
                                                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                                  erased))
                                                                                                                     else coe
                                                                                                                            seq
                                                                                                                            (coe
                                                                                                                               v28)
                                                                                                                            (coe
                                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                               (coe
                                                                                                                                  v27)
                                                                                                                               (coe
                                                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                 else coe
                                                                                                        seq
                                                                                                        (coe
                                                                                                           v25)
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                           (coe
                                                                                                              v24)
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                                             else coe
                                                                                    seq (coe v22)
                                                                                    (coe
                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                       (coe v21)
                                                                                       (coe
                                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                            else (let v20
                                                                        = seq
                                                                            (coe v19)
                                                                            (coe
                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                               (coe v18)
                                                                               (coe
                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                                                  coe
                                                                    (case coe v20 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                         -> if coe v21
                                                                              then coe
                                                                                     seq (coe v22)
                                                                                     (let v23
                                                                                            = coe
                                                                                                MAlonzo.Code.Data.List.Properties.du_'8801''45'dec_60
                                                                                                (coe
                                                                                                   MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796)
                                                                                                (coe
                                                                                                   v13)
                                                                                                (coe
                                                                                                   v15) in
                                                                                      coe
                                                                                        (case coe
                                                                                                v23 of
                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                                                             -> if coe
                                                                                                     v24
                                                                                                  then coe
                                                                                                         seq
                                                                                                         (coe
                                                                                                            v25)
                                                                                                         (let v26
                                                                                                                = coe
                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                    erased
                                                                                                                    (\ v26 ->
                                                                                                                       coe
                                                                                                                         MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                                                                                                         (coe
                                                                                                                            v14))
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                                                                                                       (coe
                                                                                                                          eqInt
                                                                                                                          (coe
                                                                                                                             v14)
                                                                                                                          (coe
                                                                                                                             v16))) in
                                                                                                          coe
                                                                                                            (case coe
                                                                                                                    v26 of
                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v27 v28
                                                                                                                 -> if coe
                                                                                                                         v27
                                                                                                                      then coe
                                                                                                                             seq
                                                                                                                             (coe
                                                                                                                                v28)
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                (coe
                                                                                                                                   v27)
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                                   erased))
                                                                                                                      else coe
                                                                                                                             seq
                                                                                                                             (coe
                                                                                                                                v28)
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                                (coe
                                                                                                                                   v27)
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                  else coe
                                                                                                         seq
                                                                                                         (coe
                                                                                                            v25)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                            (coe
                                                                                                               v24)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                                                              else coe
                                                                                     seq (coe v22)
                                                                                     (coe
                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                        (coe v21)
                                                                                        (coe
                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                     _ -> MAlonzo.RTE.mazUnreachableError)))))) in
                         coe
                           (if coe v13
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
                                              du_find'45'label'45'pres_1212 (coe v4) (coe v1)
                                              (coe v8))))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    C_hv'45'plain_470
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              addInt (coe (1 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe du_find'45'label'45'pres_1212 (coe v4) (coe v1) (coe v8))))
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
                    C_hv'45'otherlabel_488 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              addInt (coe (1 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe du_find'45'label'45'pres_1212 (coe v4) (coe v1) (coe v8))))
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.acc≡j
d_acc'8801'j_1336 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Integer ->
  Integer ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_acc'8801'j_1336 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.comp1
d_comp1_1340 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Integer ->
  Integer ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comp1_1340 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.all-headView
d_all'45'headView_1390 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'45'headView_1390 ~v0 v1 = du_all'45'headView_1390 v1
du_all'45'headView_1390 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_all'45'headView_1390 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe du_headView_508 (coe v1))
             (coe du_all'45'headView_1390 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-label-corr
d_find'45'label'45'corr_1404 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'corr_1404 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-thunk-corr
d_find'45'thunk'45'corr_1448 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'thunk'45'corr_1448 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.drop-len-++
d_drop'45'len'45''43''43'_1490 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'len'45''43''43'_1490 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.drop-[]
d_drop'45''91''93'_1504 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45''91''93'_1504 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.drop-+
d_drop'45''43'_1516 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  Integer ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45''43'_1516 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.drop-compile
d_drop'45'compile_1538 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'compile_1538 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-drop
d_fetch'45'drop_1554 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'drop_1554 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-at-offset
d_fetch'45'at'45'offset_1574 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'at'45'offset_1574 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.x86-off-suc
d_x86'45'off'45'suc_1588 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x86'45'off'45'suc_1588 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.drop-fetch
d_drop'45'fetch_1616 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'fetch_1616 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-head
d_fetch'45'block'45'head_1642 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'head_1642 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-2nd
d_fetch'45'block'45'2nd_1660 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'2nd_1660 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-3rd
d_fetch'45'block'45'3rd_1680 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'3rd_1680 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-4th
d_fetch'45'block'45'4th_1700 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'4th_1700 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-5th
d_fetch'45'block'45'5th_1720 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'5th_1720 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-6th
d_fetch'45'block'45'6th_1740 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'6th_1740 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-label-none-go
d_find'45'label'45'none'45'go_1762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'none'45'go_1762 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.absurd
d_absurd_1870 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_absurd_1870 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-label-none-corr
d_find'45'label'45'none'45'corr_1908 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'none'45'corr_1908 = erased
