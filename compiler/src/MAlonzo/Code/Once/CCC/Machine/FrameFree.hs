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

module MAlonzo.Code.Once.CCC.Machine.FrameFree where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore

-- Once.CCC.Machine.FrameFree.FrameFreeI
d_FrameFreeI_8 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 -> ()
d_FrameFreeI_8 = erased
-- Once.CCC.Machine.FrameFree.EmittableI
d_EmittableI_16 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 -> ()
d_EmittableI_16 = erased
-- Once.CCC.Machine.FrameFree.frame-free-emittable
d_frame'45'free'45'emittable_26 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  AgdaAny -> AgdaAny
d_frame'45'free'45'emittable_26 v0 ~v1
  = du_frame'45'free'45'emittable_26 v0
du_frame'45'free'45'emittable_26 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  AgdaAny
du_frame'45'free'45'emittable_26 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2238 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2244 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2250
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2252 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2254 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2256 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2258 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2264 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2270 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2272 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2274
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286 v1
        -> coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FrameFree.FrameFreeT
d_FrameFreeT_28 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> ()
d_FrameFreeT_28 = erased
-- Once.CCC.Machine.FrameFree.frame-free-++
d_frame'45'free'45''43''43'_38 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  AgdaAny -> AgdaAny -> AgdaAny
d_frame'45'free'45''43''43'_38 v0 ~v1 v2 v3
  = du_frame'45'free'45''43''43'_38 v0 v2 v3
du_frame'45'free'45''43''43'_38 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  AgdaAny -> AgdaAny -> AgdaAny
du_frame'45'free'45''43''43'_38 v0 v1 v2
  = case coe v0 of
      [] -> coe v2
      (:) v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                    (coe du_frame'45'free'45''43''43'_38 (coe v4) (coe v6) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FrameFree.frame-free-all
d_frame'45'free'45'all_60 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_frame'45'free'45'all_60 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v4
                    (d_frame'45'free'45'all_60 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FrameFree.frame-free-nest
d_frame'45'free'45'nest_74 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_frame'45'free'45'nest_74 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v4 v5
        -> case coe v0 of
             (:) v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                    (coe d_frame'45'free'45'nest_74 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FrameFree._._.exec-abstract
d_exec'45'abstract_96 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_96 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2864
      (coe v0)
-- Once.CCC.Machine.FrameFree._._.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_106 ~v0
  = du_exec'45'load'45'from'45'slot'45'with'45'value_106
du_exec'45'load'45'from'45'slot'45'with'45'value_106 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_106
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'from'45'slot'45'with'45'value_2550
-- Once.CCC.Machine.FrameFree._._.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_116 ~v0
  = du_exec'45'restore'45'input'45'with'45'value_116
du_exec'45'restore'45'input'45'with'45'value_116 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_116
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'restore'45'input'45'with'45'value_2562
-- Once.CCC.Machine.FrameFree._._.exec-trace
d_exec'45'trace_126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_126 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2866 (coe v0)
-- Once.CCC.Machine.FrameFree._.load-from-slot-alloc
d_load'45'from'45'slot'45'alloc_182 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'from'45'slot'45'alloc_182 = erased
-- Once.CCC.Machine.FrameFree._.restore-input-alloc
d_restore'45'input'45'alloc_198 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restore'45'input'45'alloc_198 = erased
-- Once.CCC.Machine.FrameFree._.exec-abstract-preserves-next-slot
d_exec'45'abstract'45'preserves'45'next'45'slot_214 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'next'45'slot_214 = erased
-- Once.CCC.Machine.FrameFree._.exec-trace-preserves-next-slot
d_exec'45'trace'45'preserves'45'next'45'slot_352 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'next'45'slot_352 = erased
-- Once.CCC.Machine.FrameFree._.load-from-slot-state
d_load'45'from'45'slot'45'state_406 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'from'45'slot'45'state_406 = erased
-- Once.CCC.Machine.FrameFree._.restore-input-state
d_restore'45'input'45'state_428 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restore'45'input'45'state_428 = erased
-- Once.CCC.Machine.FrameFree._.load-from-slot-alloc-full
d_load'45'from'45'slot'45'alloc'45'full_450 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'from'45'slot'45'alloc'45'full_450 = erased
-- Once.CCC.Machine.FrameFree._.restore-input-alloc-full
d_restore'45'input'45'alloc'45'full_472 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restore'45'input'45'alloc'45'full_472 = erased
-- Once.CCC.Machine.FrameFree._.exec-abstract-state-nsi
d_exec'45'abstract'45'state'45'nsi_494 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'state'45'nsi_494 = erased
-- Once.CCC.Machine.FrameFree._.exec-abstract-alloc-nsi
d_exec'45'abstract'45'alloc'45'nsi_696 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'alloc'45'nsi_696 = erased
-- Once.CCC.Machine.FrameFree._.exec-trace-nsi
d_exec'45'trace'45'nsi_898 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace'45'nsi_898 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
      (:) v6 v7
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> let v10
                        = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_420 (coe v2) in
                  coe
                    (if coe v10
                       then coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                       else coe
                              d_exec'45'trace'45'nsi_898 (coe v0) (coe v7)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2864
                                    (coe v0) (coe v6) (coe v2)
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_588
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                                          (coe v3))
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
                                          (coe v3))
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_580
                                          (coe v3))
                                       (coe v4)
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                                          (coe v3))
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_586
                                          (coe v3)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2864
                                    (coe v0) (coe v6) (coe v2) (coe v3)))
                              (coe v4) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
