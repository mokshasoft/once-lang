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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 -> ()
d_FrameFreeI_8 = erased
-- Once.CCC.Machine.FrameFree.EmittableI
d_EmittableI_16 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 -> ()
d_EmittableI_16 = erased
-- Once.CCC.Machine.FrameFree.ImageI
d_ImageI_24 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 -> ()
d_ImageI_24 = erased
-- Once.CCC.Machine.FrameFree.emittable-image
d_emittable'45'image_30 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  AgdaAny -> AgdaAny
d_emittable'45'image_30 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248 v2
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250 v2
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2256 v2
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2258 v2
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2260 v2
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2262 v2
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2264 v2
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2266 v2
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2268
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2272 v2
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2274 v2
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2276 v2
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2278 v2
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2284 v2 v3 v4
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2290 v2 v3 v4
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2292 v2
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296 v2
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2298 v2 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300 v2
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2302 v2
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304 v2
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306 v2
        -> coe seq (coe v2) (coe v1)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2308 v2
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FrameFree.frame-free-emittable
d_frame'45'free'45'emittable_108 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  AgdaAny -> AgdaAny
d_frame'45'free'45'emittable_108 v0 ~v1
  = du_frame'45'free'45'emittable_108 v0
du_frame'45'free'45'emittable_108 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  AgdaAny
du_frame'45'free'45'emittable_108 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2258 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2264 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2272 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2274 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2276 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2278 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2284 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2290 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2292 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306 v1
        -> coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FrameFree.FrameFreeT
d_FrameFreeT_110 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_FrameFreeT_110 = erased
-- Once.CCC.Machine.FrameFree.frame-free-++
d_frame'45'free'45''43''43'_120 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny -> AgdaAny -> AgdaAny
d_frame'45'free'45''43''43'_120 v0 ~v1 v2 v3
  = du_frame'45'free'45''43''43'_120 v0 v2 v3
du_frame'45'free'45''43''43'_120 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny -> AgdaAny -> AgdaAny
du_frame'45'free'45''43''43'_120 v0 v1 v2
  = case coe v0 of
      [] -> coe v2
      (:) v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                    (coe du_frame'45'free'45''43''43'_120 (coe v4) (coe v6) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FrameFree.frame-free-all
d_frame'45'free'45'all_142 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_frame'45'free'45'all_142 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v4
                    (d_frame'45'free'45'all_142 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FrameFree.frame-free-nest
d_frame'45'free'45'nest_156 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_frame'45'free'45'nest_156 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v4 v5
        -> case coe v0 of
             (:) v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                    (coe d_frame'45'free'45'nest_156 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FrameFree._._.exec-abstract
d_exec'45'abstract_192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_192 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
      (coe v0)
-- Once.CCC.Machine.FrameFree._._.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_202 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_202 ~v0
  = du_exec'45'load'45'from'45'slot'45'with'45'value_202
du_exec'45'load'45'from'45'slot'45'with'45'value_202 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_202
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'from'45'slot'45'with'45'value_2636
-- Once.CCC.Machine.FrameFree._._.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_212 ~v0
  = du_exec'45'restore'45'input'45'with'45'value_212
du_exec'45'restore'45'input'45'with'45'value_212 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_212
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'restore'45'input'45'with'45'value_2648
-- Once.CCC.Machine.FrameFree._._.exec-trace
d_exec'45'trace_222 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_222 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_3230 (coe v0)
-- Once.CCC.Machine.FrameFree._.load-from-slot-alloc
d_load'45'from'45'slot'45'alloc_294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'from'45'slot'45'alloc_294 = erased
-- Once.CCC.Machine.FrameFree._.restore-input-alloc
d_restore'45'input'45'alloc_310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restore'45'input'45'alloc_310 = erased
-- Once.CCC.Machine.FrameFree._.exec-abstract-preserves-next-slot
d_exec'45'abstract'45'preserves'45'next'45'slot_326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'next'45'slot_326 = erased
-- Once.CCC.Machine.FrameFree._.exec-trace-preserves-next-slot
d_exec'45'trace'45'preserves'45'next'45'slot_464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'next'45'slot_464 = erased
-- Once.CCC.Machine.FrameFree._.load-from-slot-state
d_load'45'from'45'slot'45'state_518 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'from'45'slot'45'state_518 = erased
-- Once.CCC.Machine.FrameFree._.restore-input-state
d_restore'45'input'45'state_540 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restore'45'input'45'state_540 = erased
-- Once.CCC.Machine.FrameFree._.load-from-slot-alloc-full
d_load'45'from'45'slot'45'alloc'45'full_562 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'from'45'slot'45'alloc'45'full_562 = erased
-- Once.CCC.Machine.FrameFree._.restore-input-alloc-full
d_restore'45'input'45'alloc'45'full_584 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restore'45'input'45'alloc'45'full_584 = erased
-- Once.CCC.Machine.FrameFree._.exec-abstract-state-nsi
d_exec'45'abstract'45'state'45'nsi_606 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'state'45'nsi_606 = erased
-- Once.CCC.Machine.FrameFree._.exec-abstract-alloc-nsi
d_exec'45'abstract'45'alloc'45'nsi_808 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'alloc'45'nsi_808 = erased
-- Once.CCC.Machine.FrameFree._.exec-trace-nsi
d_exec'45'trace'45'nsi_1010 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace'45'nsi_1010 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
      (:) v6 v7
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> let v10
                        = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_422 (coe v2) in
                  coe
                    (if coe v10
                       then coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                       else coe
                              d_exec'45'trace'45'nsi_1010 (coe v0) (coe v7)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
                                    (coe v0) (coe v6) (coe v2)
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_596
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                                          (coe v3))
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_586
                                          (coe v3))
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_588
                                          (coe v3))
                                       (coe v4)
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                                          (coe v3))
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_594
                                          (coe v3)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
                                    (coe v0) (coe v6) (coe v2) (coe v3)))
                              (coe v4) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
