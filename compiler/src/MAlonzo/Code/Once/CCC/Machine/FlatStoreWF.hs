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

module MAlonzo.Code.Once.CCC.Machine.FlatStoreWF where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Machine.FlatStoreWF._.readLoc
d_readLoc_20 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_readLoc_20 ~v0 = du_readLoc_20
du_readLoc_20 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_readLoc_20
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766
-- Once.CCC.Machine.FlatStoreWF._.writeHeapMem-aux
d_writeHeapMem'45'aux_26 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_writeHeapMem'45'aux_26 ~v0 = du_writeHeapMem'45'aux_26
du_writeHeapMem'45'aux_26 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_writeHeapMem'45'aux_26 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem'45'aux_812 v2
      v3 v4
-- Once.CCC.Machine.FlatStoreWF._.writeLoc
d_writeLoc_28 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_writeLoc_28 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_846 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.writeLocToHeap
d_writeLocToHeap_44 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_writeLocToHeap_44 ~v0 = du_writeLocToHeap_44
du_writeLocToHeap_44 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
du_writeLocToHeap_44
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_838
-- Once.CCC.Machine.FlatStoreWF._.writeLocToStack
d_writeLocToStack_46 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_writeLocToStack_46 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLocToStack_828 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.writeStackMem-aux
d_writeStackMem'45'aux_50 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_writeStackMem'45'aux_50 ~v0 = du_writeStackMem'45'aux_50
du_writeStackMem'45'aux_50 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_writeStackMem'45'aux_50 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeStackMem'45'aux_786 v4
      v5 v6 v7
-- Once.CCC.Machine.FlatStoreWF._.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_56 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_exec'45'lea'45'indexed'45'via_56 ~v0
  = du_exec'45'lea'45'indexed'45'via_56
du_exec'45'lea'45'indexed'45'via_56 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
du_exec'45'lea'45'indexed'45'via_56
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'lea'45'indexed'45'via_1520
-- Once.CCC.Machine.FlatStoreWF._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_62 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_exec'45'load'45'suc'45'via'45'resolved_62 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_62
du_exec'45'load'45'suc'45'via'45'resolved_62 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
du_exec'45'load'45'suc'45'via'45'resolved_62
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'suc'45'via'45'resolved_1532
-- Once.CCC.Machine.FlatStoreWF._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_64 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_exec'45'load'45'via'45'resolved_64 ~v0
  = du_exec'45'load'45'via'45'resolved_64
du_exec'45'load'45'via'45'resolved_64 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
du_exec'45'load'45'via'45'resolved_64
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'via'45'resolved_1494
-- Once.CCC.Machine.FlatStoreWF._.exec-load-with-value
d_exec'45'load'45'with'45'value_66 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_exec'45'load'45'with'45'value_66 ~v0
  = du_exec'45'load'45'with'45'value_66
du_exec'45'load'45'with'45'value_66 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
du_exec'45'load'45'with'45'value_66
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'with'45'value_1482
-- Once.CCC.Machine.FlatStoreWF._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_68 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_exec'45'store'45'suc'45'via'45'resolved_68 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'suc'45'via'45'resolved_1544
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_70 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_exec'45'store'45'via'45'resolved_70 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'via'45'resolved_1506
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.slot-base
d_slot'45'base_74 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_74 ~v0 = du_slot'45'base_74
du_slot'45'base_74 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_74
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_slot'45'base_1516
-- Once.CCC.Machine.FlatStoreWF._.BodyRunner
d_BodyRunner_80 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_BodyRunner_80 = erased
-- Once.CCC.Machine.FlatStoreWF._.exec-abstract
d_exec'45'abstract_86 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_86 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2816
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.exec-case-dispatch
d_exec'45'case'45'dispatch_90 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'case'45'dispatch_90 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'case'45'dispatch_2822
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_96 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_96 ~v0
  = du_exec'45'load'45'from'45'slot'45'with'45'value_96
du_exec'45'load'45'from'45'slot'45'with'45'value_96 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_96
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'from'45'slot'45'with'45'value_2512
-- Once.CCC.Machine.FlatStoreWF._.exec-loop-run
d_exec'45'loop'45'run_100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop'45'run_100 ~v0 = du_exec'45'loop'45'run_100
du_exec'45'loop'45'run_100 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'loop'45'run_100
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'loop'45'run_2760
-- Once.CCC.Machine.FlatStoreWF._.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_106 ~v0
  = du_exec'45'restore'45'input'45'with'45'value_106
du_exec'45'restore'45'input'45'with'45'value_106 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_106
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'restore'45'input'45'with'45'value_2524
-- Once.CCC.Machine.FlatStoreWF._.exec-sigop-output
d_exec'45'sigop'45'output_112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_exec'45'sigop'45'output_112 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output_2710
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_114 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_exec'45'sigop'45'output'45'of_114 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output'45'of_2700
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.exec-trace
d_exec'45'trace_116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_116 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2818 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.loop-reanchor-alloc
d_loop'45'reanchor'45'alloc_142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_loop'45'reanchor'45'alloc_142 ~v0
  = du_loop'45'reanchor'45'alloc_142
du_loop'45'reanchor'45'alloc_142 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
du_loop'45'reanchor'45'alloc_142
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'alloc_2754
-- Once.CCC.Machine.FlatStoreWF._.loop-reanchor-loc
d_loop'45'reanchor'45'loc_144 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_loop'45'reanchor'45'loc_144 ~v0 = du_loop'45'reanchor'45'loc_144
du_loop'45'reanchor'45'loc_144 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
du_loop'45'reanchor'45'loc_144
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'loc_2748
-- Once.CCC.Machine.FlatStoreWF._.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_146 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_pure'45'sigop'45'out'45'aux_146 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'aux_2664
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_pure'45'sigop'45'out'45'val_148 ~v0
  = du_pure'45'sigop'45'out'45'val_148
du_pure'45'sigop'45'out'45'val_148 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_pure'45'sigop'45'out'45'val_148 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_pure'45'sigop'45'out'45'val_2648
      v1 v2 v3 v4
-- Once.CCC.Machine.FlatStoreWF._.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_structured'45'pure'45'sigop'45'output_160 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_structured'45'pure'45'sigop'45'output_2636
      v0
-- Once.CCC.Machine.FlatStoreWF._.FlatState
d_FlatState_166 a0 = ()
-- Once.CCC.Machine.FlatStoreWF._.do-branch
d_do'45'branch_174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_do'45'branch_174 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'branch_164 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.do-jump
d_do'45'jump_176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_do'45'jump_176 ~v0 = du_do'45'jump_176
du_do'45'jump_176 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_do'45'jump_176
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_156
-- Once.CCC.Machine.FlatStoreWF._.flat-exec-instr
d_flat'45'exec'45'instr_212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_flat'45'exec'45'instr_212 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_262
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.FlatState.falloc
d_falloc_252 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_falloc_252 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.FlatState.floc
d_floc_254 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_floc_254 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.FlatState.fpc
d_fpc_256 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> Integer
d_fpc_256 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_74 (coe v0)
-- Once.CCC.Machine.FlatStoreWF.loc-below
d_loc'45'below_258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_loc'45'below_258 = erased
-- Once.CCC.Machine.FlatStoreWF.sv-below
d_sv'45'below_266 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_sv'45'below_266 = erased
-- Once.CCC.Machine.FlatStoreWF.svm-below
d_svm'45'below_278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_svm'45'below_278 = erased
-- Once.CCC.Machine.FlatStoreWF.mloc-below
d_mloc'45'below_286 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  ()
d_mloc'45'below_286 = erased
-- Once.CCC.Machine.FlatStoreWF.loc-mono
d_loc'45'mono_300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_loc'45'mono_300 ~v0 ~v1 ~v2 v3 v4 v5
  = du_loc'45'mono_300 v3 v4 v5
du_loc'45'mono_300 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_loc'45'mono_300 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v2)
             (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.sv-mono
d_sv'45'mono_314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_sv'45'mono_314 ~v0 ~v1 ~v2 v3 v4 v5 = du_sv'45'mono_314 v3 v4 v5
du_sv'45'mono_314 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_sv'45'mono_314 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v3
        -> coe du_loc'45'mono_300 (coe v3) (coe v1) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.svm-mono
d_svm'45'mono_328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_svm'45'mono_328 ~v0 ~v1 ~v2 v3 v4 v5
  = du_svm'45'mono_328 v3 v4 v5
du_svm'45'mono_328 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_svm'45'mono_328 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe du_sv'45'mono_314 (coe v3) (coe v1) (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.sv-as-loc-below
d_sv'45'as'45'loc'45'below_340 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny
d_sv'45'as'45'loc'45'below_340 ~v0 ~v1 v2 v3
  = du_sv'45'as'45'loc'45'below_340 v2 v3
du_sv'45'as'45'loc'45'below_340 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny
du_sv'45'as'45'loc'45'below_340 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v2
        -> case coe v2 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.slot-base-below
d_slot'45'base'45'below_366 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny
d_slot'45'base'45'below_366 ~v0 ~v1 v2 v3
  = du_slot'45'base'45'below_366 v2 v3
du_slot'45'base'45'below_366 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny
du_slot'45'base'45'below_366 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe du_sv'45'as'45'loc'45'below_340 (coe v2) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.sucLoc-below
d_sucLoc'45'below_380 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> AgdaAny
d_sucLoc'45'below_380 ~v0 ~v1 v2 v3 = du_sucLoc'45'below_380 v2 v3
du_sucLoc'45'below_380 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> AgdaAny
du_sucLoc'45'below_380 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe seq (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.offsetLoc-below
d_offsetLoc'45'below_402 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> AgdaAny -> AgdaAny
d_offsetLoc'45'below_402 ~v0 ~v1 v2 ~v3 v4
  = du_offsetLoc'45'below_402 v2 v4
du_offsetLoc'45'below_402 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> AgdaAny
du_offsetLoc'45'below_402 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe seq (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.sv-succ-below
d_sv'45'succ'45'below_426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
d_sv'45'succ'45'below_426 ~v0 ~v1 v2
  = du_sv'45'succ'45'below_426 v2
du_sv'45'succ'45'below_426 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
du_sv'45'succ'45'below_426 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatStoreWF.sv-pred-below
d_sv'45'pred'45'below_440 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
d_sv'45'pred'45'below_440 ~v0 ~v1 v2
  = du_sv'45'pred'45'below_440 v2
du_sv'45'pred'45'below_440 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
du_sv'45'pred'45'below_440 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v1
        -> coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.StoreWF
d_StoreWF_456 a0 a1 a2 = ()
data T_StoreWF_456
  = C_constructor_498 (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
                       AgdaAny)
                      (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny)
                      (AgdaAny -> Integer -> AgdaAny)
-- Once.CCC.Machine.FlatStoreWF.StoreWF.wf-regs
d_wf'45'regs_482 ::
  T_StoreWF_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
d_wf'45'regs_482 v0
  = case coe v0 of
      C_constructor_498 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.StoreWF.wf-heap
d_wf'45'heap_486 ::
  T_StoreWF_456 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny
d_wf'45'heap_486 v0
  = case coe v0 of
      C_constructor_498 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.StoreWF.wf-stack
d_wf'45'stack_492 :: T_StoreWF_456 -> AgdaAny -> Integer -> AgdaAny
d_wf'45'stack_492 v0
  = case coe v0 of
      C_constructor_498 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.StoreWF.wf-fresh
d_wf'45'fresh_496 ::
  T_StoreWF_456 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wf'45'fresh_496 = erased
-- Once.CCC.Machine.FlatStoreWF.rw-below
d_rw'45'below_510 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_126 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_rw'45'below_510 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du_rw'45'below_510 v3 v4 v6 v7
du_rw'45'below_510 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_rw'45'below_510 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56 -> coe v2
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64 -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58 -> coe v2
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64 -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60 -> coe v2
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64 -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62 -> coe v2
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64 -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64 -> coe v2
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-write-reg
d_wf'45'write'45'reg_720 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_StoreWF_456 -> AgdaAny -> T_StoreWF_456
d_wf'45'write'45'reg_720 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_wf'45'write'45'reg_720 v3 v5 v6
du_wf'45'write'45'reg_720 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  T_StoreWF_456 -> AgdaAny -> T_StoreWF_456
du_wf'45'write'45'reg_720 v0 v1 v2
  = coe
      C_constructor_498
      (\ v3 ->
         coe
           du_rw'45'below_510 (coe v0) (coe v3) (coe v2)
           (coe d_wf'45'regs_482 v1 v3))
      (d_wf'45'heap_486 (coe v1)) (d_wf'45'stack_492 (coe v1))
-- Once.CCC.Machine.FlatStoreWF.wf-halt
d_wf'45'halt_740 :: T_StoreWF_456 -> T_StoreWF_456
d_wf'45'halt_740 v0 = coe v0
-- Once.CCC.Machine.FlatStoreWF.wf-write-reg-halt
d_wf'45'write'45'reg'45'halt_754 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Bool -> T_StoreWF_456 -> AgdaAny -> T_StoreWF_456
d_wf'45'write'45'reg'45'halt_754 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du_wf'45'write'45'reg'45'halt_754 v3 v6 v7
du_wf'45'write'45'reg'45'halt_754 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  T_StoreWF_456 -> AgdaAny -> T_StoreWF_456
du_wf'45'write'45'reg'45'halt_754 v0 v1 v2
  = coe
      C_constructor_498
      (\ v3 ->
         coe
           du_rw'45'below_510 (coe v0) (coe v3) (coe v2)
           (coe d_wf'45'regs_482 v1 v3))
      (d_wf'45'heap_486 (coe v1)) (d_wf'45'stack_492 (coe v1))
-- Once.CCC.Machine.FlatStoreWF.regs-ss
d_regs'45'ss_780 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_126 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> AgdaAny
d_regs'45'ss_780 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_regs'45'ss_780 v4 v5
du_regs'45'ss_780 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> AgdaAny
du_regs'45'ss_780 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatStoreWF.wf-stack-slot
d_wf'45'stack'45'slot_828 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  Integer -> T_StoreWF_456 -> T_StoreWF_456
d_wf'45'stack'45'slot_828 ~v0 ~v1 ~v2 ~v3 v4
  = du_wf'45'stack'45'slot_828 v4
du_wf'45'stack'45'slot_828 :: T_StoreWF_456 -> T_StoreWF_456
du_wf'45'stack'45'slot_828 v0
  = coe
      C_constructor_498
      (\ v1 ->
         coe du_regs'45'ss_780 (coe v1) (coe d_wf'45'regs_482 v0 v1))
      (d_wf'45'heap_486 (coe v0)) (d_wf'45'stack_492 (coe v0))
-- Once.CCC.Machine.FlatStoreWF.wsm-below
d_wsm'45'below_858 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_wsm'45'below_858 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 v10 v11
  = du_wsm'45'below_858 v6 v7 v10 v11
du_wsm'45'below_858 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_wsm'45'below_858 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                         -> if coe v6
                              then coe seq (coe v7) (coe v3)
                              else coe seq (coe v7) (coe v2)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe seq (coe v5) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-write-stack
d_wf'45'write'45'stack_894 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_StoreWF_456 -> AgdaAny -> T_StoreWF_456
d_wf'45'write'45'stack_894 v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du_wf'45'write'45'stack_894 v0 v3 v4 v6 v7
du_wf'45'write'45'stack_894 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> T_StoreWF_456 -> AgdaAny -> T_StoreWF_456
du_wf'45'write'45'stack_894 v0 v1 v2 v3 v4
  = coe
      C_constructor_498 (d_wf'45'regs_482 (coe v3))
      (d_wf'45'heap_486 (coe v3))
      (\ v5 v6 ->
         coe
           du_wsm'45'below_858
           (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__84 v0 v1 v5)
           (coe
              MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v2) (coe v6))
           (coe d_wf'45'stack_492 v3 v5 v6) (coe v4))
-- Once.CCC.Machine.FlatStoreWF.whm-below
d_whm'45'below_926 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_whm'45'below_926 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8
  = du_whm'45'below_926 v4 v7 v8
du_whm'45'below_926 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_whm'45'below_926 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe seq (coe v4) (coe v2)
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.whm-fresh
d_whm'45'fresh_956 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_whm'45'fresh_956 = erased
-- Once.CCC.Machine.FlatStoreWF.wf-write-heap
d_wf'45'write'45'heap_986 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_StoreWF_456 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> T_StoreWF_456
d_wf'45'write'45'heap_986 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7
  = du_wf'45'write'45'heap_986 v3 v5 v7
du_wf'45'write'45'heap_986 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoreWF_456 -> AgdaAny -> T_StoreWF_456
du_wf'45'write'45'heap_986 v0 v1 v2
  = coe
      C_constructor_498 (d_wf'45'regs_482 (coe v1))
      (\ v3 ->
         coe
           du_whm'45'below_926
           (coe
              MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__80 (coe v0)
              (coe v3))
           (coe d_wf'45'heap_486 v1 v3) (coe v2))
      (d_wf'45'stack_492 (coe v1))
-- Once.CCC.Machine.FlatStoreWF.wf-write-loc
d_wf'45'write'45'loc_1016 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_StoreWF_456 -> AgdaAny -> AgdaAny -> T_StoreWF_456
d_wf'45'write'45'loc_1016 v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_wf'45'write'45'loc_1016 v0 v3 v4 v5 v7
du_wf'45'write'45'loc_1016 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_StoreWF_456 -> AgdaAny -> T_StoreWF_456
du_wf'45'write'45'loc_1016 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v5 v6
        -> coe
             du_wf'45'write'45'stack_894 (coe v0) (coe v5) (coe v6) (coe v3)
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v5
        -> case coe v2 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v6
               -> coe
                    seq (coe v6)
                    (coe du_wf'45'write'45'heap_986 (coe v5) (coe v3) (coe v4))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v6
               -> coe du_wf'45'write'45'heap_986 (coe v5) (coe v3) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v6 v7 v8
               -> coe du_wf'45'write'45'heap_986 (coe v5) (coe v3) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v6
               -> coe du_wf'45'write'45'heap_986 (coe v5) (coe v3) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.readLoc-below
d_readLoc'45'below_1088 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_456 -> AgdaAny
d_readLoc'45'below_1088 ~v0 ~v1 ~v2 v3 v4
  = du_readLoc'45'below_1088 v3 v4
du_readLoc'45'below_1088 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_456 -> AgdaAny
du_readLoc'45'below_1088 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe d_wf'45'stack_492 v1 v2 v3
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe d_wf'45'heap_486 v1 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-load-value
d_wf'45'load'45'value_1108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_StoreWF_456 -> AgdaAny -> T_StoreWF_456
d_wf'45'load'45'value_1108 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_wf'45'load'45'value_1108 v3 v4 v5 v6
du_wf'45'load'45'value_1108 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_StoreWF_456 -> AgdaAny -> T_StoreWF_456
du_wf'45'load'45'value_1108 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe du_wf'45'write'45'reg_720 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-load-resolved
d_wf'45'load'45'resolved_1130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_456 -> AgdaAny -> T_StoreWF_456
d_wf'45'load'45'resolved_1130 ~v0 ~v1 v2 v3 v4 v5 ~v6
  = du_wf'45'load'45'resolved_1130 v2 v3 v4 v5
du_wf'45'load'45'resolved_1130 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_456 -> T_StoreWF_456
du_wf'45'load'45'resolved_1130 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_wf'45'load'45'value_1108 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v0)
                (coe v4))
             (coe v3) (coe du_readLoc'45'below_1088 (coe v4) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-load-suc-resolved
d_wf'45'load'45'suc'45'resolved_1150 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_456 -> AgdaAny -> T_StoreWF_456
d_wf'45'load'45'suc'45'resolved_1150 ~v0 ~v1 v2 v3 v4 v5 ~v6
  = du_wf'45'load'45'suc'45'resolved_1150 v2 v3 v4 v5
du_wf'45'load'45'suc'45'resolved_1150 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_456 -> T_StoreWF_456
du_wf'45'load'45'suc'45'resolved_1150 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_wf'45'load'45'value_1108 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v0)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v4)))
             (coe v3)
             (coe
                du_readLoc'45'below_1088
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v4))
                (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-store-resolved
d_wf'45'store'45'resolved_1176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_StoreWF_456 -> AgdaAny -> AgdaAny -> T_StoreWF_456
d_wf'45'store'45'resolved_1176 v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_wf'45'store'45'resolved_1176 v0 v3 v4 v5 v7
du_wf'45'store'45'resolved_1176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_StoreWF_456 -> AgdaAny -> T_StoreWF_456
du_wf'45'store'45'resolved_1176 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_wf'45'write'45'loc_1016 (coe v0) (coe v5) (coe v2) (coe v3)
             (coe v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-store-suc-resolved
d_wf'45'store'45'suc'45'resolved_1200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_StoreWF_456 -> AgdaAny -> AgdaAny -> T_StoreWF_456
d_wf'45'store'45'suc'45'resolved_1200 v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_wf'45'store'45'suc'45'resolved_1200 v0 v3 v4 v5 v7
du_wf'45'store'45'suc'45'resolved_1200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_StoreWF_456 -> AgdaAny -> T_StoreWF_456
du_wf'45'store'45'suc'45'resolved_1200 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_wf'45'write'45'loc_1016 (coe v0)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v5))
             (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-lea-indexed
d_wf'45'lea'45'indexed_1228 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_StoreWF_456 -> AgdaAny -> T_StoreWF_456
d_wf'45'lea'45'indexed_1228 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_wf'45'lea'45'indexed_1228 v3 v5 v6
du_wf'45'lea'45'indexed_1228 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_456 -> AgdaAny -> T_StoreWF_456
du_wf'45'lea'45'indexed_1228 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_wf'45'write'45'reg_720
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v1)
             (coe du_offsetLoc'45'below_402 (coe v3) (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-slot-load
d_wf'45'slot'45'load_1254 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_StoreWF_456 -> AgdaAny -> T_StoreWF_456
d_wf'45'slot'45'load_1254 ~v0 ~v1 ~v2 = du_wf'45'slot'45'load_1254
du_wf'45'slot'45'load_1254 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_StoreWF_456 -> AgdaAny -> T_StoreWF_456
du_wf'45'slot'45'load_1254 = coe du_wf'45'load'45'value_1108
-- Once.CCC.Machine.FlatStoreWF.structured-pure-sigop-below
d_structured'45'pure'45'sigop'45'below_1266
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.FlatStoreWF.structured-pure-sigop-below"
-- Once.CCC.Machine.FlatStoreWF.pure-out-val-below
d_pure'45'out'45'val'45'below_1280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 -> Maybe AgdaAny -> AgdaAny
d_pure'45'out'45'val'45'below_1280 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_pure'45'out'45'val'45'below_1280 v6
du_pure'45'out'45'val'45'below_1280 :: Maybe AgdaAny -> AgdaAny
du_pure'45'out'45'val'45'below_1280 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatStoreWF.sigop-output-below
d_sigop'45'output'45'below_1306 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 -> AgdaAny
d_sigop'45'output'45'below_1306 v0 v1 v2 v3 v4 v5
  = coe
      d_go_1336 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_212 (coe v4))
-- Once.CCC.Machine.FlatStoreWF._.aux
d_aux_1326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
d_aux_1326 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> coe
                    du_pure'45'out'45'val'45'below_1280
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2606 (coe v2)
                       (coe v9) (coe v5))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    du_pure'45'out'45'val'45'below_1280
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg'45'typed_2600
                       (coe v2)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v5))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             d_structured'45'pure'45'sigop'45'below_1266 v0 v1 v2 v3 v4 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF._.go
d_go_1336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 -> AgdaAny
d_go_1336 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_124
        -> coe
             d_aux_1326 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_204 (coe v3))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1396
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v5))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
      MAlonzo.Code.Once.SigOp.Info.C_Emits_126
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.SigOp.Info.C_Halts_128
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-slot-load-out
d_wf'45'slot'45'load'45'out_1344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  T_StoreWF_456 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'slot'45'load'45'out_1344 ~v0 v1 ~v2 v3 v4 v5
  = du_wf'45'slot'45'load'45'out_1344 v1 v3 v4 v5
du_wf'45'slot'45'load'45'out_1344 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  T_StoreWF_456 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf'45'slot'45'load'45'out_1344 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_720
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v2)
                (coe v3))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v1)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-slot-load-in1
d_wf'45'slot'45'load'45'in1_1368 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  T_StoreWF_456 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'slot'45'load'45'in1_1368 ~v0 v1 ~v2 v3 v4 v5
  = du_wf'45'slot'45'load'45'in1_1368 v1 v3 v4 v5
du_wf'45'slot'45'load'45'in1_1368 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  T_StoreWF_456 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf'45'slot'45'load'45'in1_1368 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_720
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v2)
                (coe v3))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v1)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.Preserves
d_Preserves_1390 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_Preserves_1390 = erased
-- Once.CCC.Machine.FlatStoreWF.BodyPreserves
d_BodyPreserves_1400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  ()
d_BodyPreserves_1400 = erased
-- Once.CCC.Machine.FlatStoreWF.wf-loop-run
d_wf'45'loop'45'run_1416 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   T_StoreWF_456 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_456 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'loop'45'run_1416 v0 v1 v2 v3 v4 v5 v6
  = case coe v2 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v4)))
      _ -> let v7 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (let v8
                    = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_558 (coe v3) in
              coe
                (if coe v8
                   then coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                                (coe v4)))
                   else (let v9
                               = MAlonzo.Code.Once.CCC.Machine.SMCore.d_scratch_150
                                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v3)) in
                         coe
                           (case coe v9 of
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v10
                                -> coe
                                     d_wf'45'loop'45'run'45'go_1426 (coe v0) (coe v1) (coe v7)
                                     (coe v3) (coe v4) (coe v5) (coe v6)
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v10
                                -> case coe v10 of
                                     0 -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                            (coe
                                               MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                                                  (coe v4)))
                                     _ -> coe
                                            d_wf'45'loop'45'run'45'go_1426 (coe v0) (coe v1)
                                            (coe v7) (coe v3) (coe v4) (coe v5) (coe v6)
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v10 v11 v12
                                -> coe
                                     d_wf'45'loop'45'run'45'go_1426 (coe v0) (coe v1) (coe v7)
                                     (coe v3) (coe v4) (coe v5) (coe v6)
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v10
                                -> coe
                                     d_wf'45'loop'45'run'45'go_1426 (coe v0) (coe v1) (coe v7)
                                     (coe v3) (coe v4) (coe v5) (coe v6)
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Machine.FlatStoreWF.wf-loop-run-go
d_wf'45'loop'45'run'45'go_1426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   T_StoreWF_456 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_456 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'loop'45'run'45'go_1426 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_rec_1572 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v6)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe du_step_1560 (coe v3) (coe v4) (coe v5) (coe v6)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_rec_1572 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6))))
-- Once.CCC.Machine.FlatStoreWF._.step
d_step_1560 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   T_StoreWF_456 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_456 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_1560 ~v0 ~v1 ~v2 v3 v4 v5 v6 = du_step_1560 v3 v4 v5 v6
du_step_1560 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   T_StoreWF_456 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_456 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_1560 v0 v1 v2 v3 = coe v2 v0 v1 v3
-- Once.CCC.Machine.FlatStoreWF._.ls''
d_ls''''_1562 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   T_StoreWF_456 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_ls''''_1562 ~v0 v1 ~v2 v3 v4 ~v5 ~v6 = du_ls''''_1562 v1 v3 v4
du_ls''''_1562 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
du_ls''''_1562 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'loc_2748
      (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0 v1 v2))
-- Once.CCC.Machine.FlatStoreWF._.al''
d_al''''_1564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   T_StoreWF_456 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_al''''_1564 ~v0 v1 ~v2 v3 v4 ~v5 ~v6 = du_al''''_1564 v1 v3 v4
du_al''''_1564 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
du_al''''_1564 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'alloc_2754
      (coe v2)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0 v1 v2))
-- Once.CCC.Machine.FlatStoreWF._.wf''
d_wf''''_1566 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   T_StoreWF_456 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_456 -> T_StoreWF_456
d_wf''''_1566 ~v0 ~v1 ~v2 v3 v4 v5 v6 = du_wf''''_1566 v3 v4 v5 v6
du_wf''''_1566 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   T_StoreWF_456 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_456 -> T_StoreWF_456
du_wf''''_1566 v0 v1 v2 v3
  = coe
      C_constructor_498
      (d_wf'45'regs_482
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe du_step_1560 (coe v0) (coe v1) (coe v2) (coe v3))))
      (d_wf'45'heap_486
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe du_step_1560 (coe v0) (coe v1) (coe v2) (coe v3))))
      (\ v4 v5 ->
         coe
           du_svm'45'mono_328
           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_554 v0 v4 v5)
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
              (coe du_step_1560 (coe v0) (coe v1) (coe v2) (coe v3)))
           (coe d_wf'45'stack_492 v3 v4 v5))
-- Once.CCC.Machine.FlatStoreWF._.rec
d_rec_1572 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   T_StoreWF_456 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_456 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rec_1572 v0 v1 v2 v3 v4 v5 v6
  = coe
      d_wf'45'loop'45'run_1416 (coe v0) (coe v1) (coe v2)
      (coe du_ls''''_1562 (coe v1) (coe v3) (coe v4))
      (coe du_al''''_1564 (coe v1) (coe v3) (coe v4)) (coe v5)
      (coe du_wf''''_1566 (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.CCC.Machine.FlatStoreWF.wf-abstract
d_wf'45'abstract_1580 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  T_StoreWF_456 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'abstract_1580 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_720
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
                (coe
                   d_wf'45'regs_482 v4
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_720
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v4)
                (coe
                   d_wf'45'regs_482 v4
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2244
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_720
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58) (coe v4)
                (coe
                   d_wf'45'regs_482 v4
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2246
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_720
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
                (coe
                   d_wf'45'regs_482 v4
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2248
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'load'45'resolved_1130 (coe v2)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1396
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                (coe v4))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2250
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'load'45'suc'45'resolved_1150 (coe v2)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1396
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                (coe v4))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2252 v5
        -> coe
             du_wf'45'slot'45'load'45'out_1344
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                      (coe v3))
                   (coe v5)))
             (coe v3) (coe v4)
             (coe
                du_readLoc'45'below_1088
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                      (coe v3))
                   (coe v5))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2254 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'loc_1016 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                      (coe v3))
                   (coe v5))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                (coe v4)
                (coe
                   d_wf'45'regs_482 v4
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2256
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'store'45'resolved_1176 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1396
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                (coe v4)
                (coe
                   d_wf'45'regs_482 v4
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2258
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'store'45'suc'45'resolved_1200 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1396
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                (coe v4)
                (coe
                   d_wf'45'regs_482 v4
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2260 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_720
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2262 v5
        -> coe
             du_wf'45'slot'45'load'45'in1_1368
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                      (coe v3))
                   (coe v5)))
             (coe v3) (coe v4)
             (coe
                du_readLoc'45'below_1088
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                      (coe v3))
                   (coe v5))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2264 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_wf'45'stack'45'slot_828 (coe v4))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2266 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_wf'45'stack'45'slot_828 (coe v4))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2268 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2270 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_wf'45'stack'45'slot_828 (coe v4))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2272
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2274
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2276 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2278 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'loc_1016 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                      (coe v3))
                   (coe v5))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                (coe v4)
                (coe
                   d_wf'45'regs_482 v4
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2280 v5
        -> coe
             du_wf'45'slot'45'load'45'out_1344
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                      (coe v3))
                   (coe v5)))
             (coe v3) (coe v4)
             (coe
                du_readLoc'45'below_1088
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                      (coe v3))
                   (coe v5))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2282 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2288 v5 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg'45'halt_754
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
                (coe
                   d_sigop'45'output'45'below_1306 (coe v0)
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                      (coe v3))
                   (coe v5) (coe v6) (coe v7) (coe v2)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2292 v5 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_720
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2294 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_720
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2296
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2298 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_720
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2300 v5 v6
        -> coe
             d_wf'45'case_1600 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_case'45'tag'45'at_2732
                (coe v2))
             (coe v5) (coe v6) (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2302 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_constructor_498
                (\ v6 ->
                   coe
                     du_rw'45'below_510
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v6)
                     (coe
                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                        (coe
                           addInt (coe (1 :: Integer))
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                              (coe v3))))
                     (coe
                        du_sv'45'mono_314
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                           (coe v6))
                        (coe
                           MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                              (coe v3)))
                        (coe d_wf'45'regs_482 v4 v6)))
                (\ v6 ->
                   coe
                     du_svm'45'mono_328
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_556 v2 v6)
                     (coe
                        MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                           (coe v3)))
                     (coe d_wf'45'heap_486 v4 v6))
                (\ v6 v7 ->
                   coe
                     du_svm'45'mono_328
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_554 v2 v6 v7)
                     (coe
                        MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                           (coe v3)))
                     (coe d_wf'45'stack_492 v4 v6 v7)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2304 v5
        -> coe
             d_wf'45'loop'45'run_1416 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2818 (coe v0)
                (coe v5))
             (coe (1000000 :: Integer)) (coe v2) (coe v3)
             (coe d_wf'45'trace_1588 (coe v0) (coe v5)) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2306 v5
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_508
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_wf'45'write'45'reg_720
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62) (coe v4)
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                          (coe v3)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_510
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_wf'45'write'45'reg_720
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62) (coe v4)
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                          (coe v3)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_512
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_wf'45'write'45'reg_720
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62) (coe v4)
                       (coe
                          du_sv'45'pred'45'below_440
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62))))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                          (coe v3)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_514
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_wf'45'write'45'reg_720
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62) (coe v4)
                       (coe
                          d_wf'45'regs_482 v4
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64)))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                          (coe v3)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_516
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_wf'45'write'45'reg_720
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64) (coe v4)
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                          (coe v3)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_518
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_wf'45'write'45'reg_720
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64) (coe v4)
                       (coe
                          du_sv'45'succ'45'below_426
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64))))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                          (coe v3)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2308 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2310 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'lea'45'indexed_1228
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_slot'45'base_1516
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v2)
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                            (coe v3))
                         (coe v5))))
                (coe v4)
                (coe
                   du_slot'45'base'45'below_366
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v2)
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                            (coe v3))
                         (coe v5)))
                   (coe
                      du_readLoc'45'below_1088
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                            (coe v3))
                         (coe v5))
                      (coe v4))))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-trace
d_wf'45'trace_1588 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  T_StoreWF_456 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'trace_1588 v0 v1 v2 v3 v4
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v3)))
      (:) v5 v6
        -> let v7
                 = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_558 (coe v2) in
           coe
             (if coe v7
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                             (coe v3)))
                else coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_wf'45'trace_1588 (coe v0) (coe v6)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2816
                                   (coe v0) (coe v5) (coe v2) (coe v3)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2816
                                   (coe v0) (coe v5) (coe v2) (coe v3)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   d_wf'45'abstract_1580 (coe v0) (coe v5) (coe v2) (coe v3)
                                   (coe v4)))))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_wf'45'abstract_1580 (coe v0) (coe v5) (coe v2) (coe v3)
                                (coe v4)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_wf'45'trace_1588 (coe v0) (coe v6)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2816
                                      (coe v0) (coe v5) (coe v2) (coe v3)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2816
                                      (coe v0) (coe v5) (coe v2) (coe v3)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_wf'45'abstract_1580 (coe v0) (coe v5) (coe v2) (coe v3)
                                      (coe v4)))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-case
d_wf'45'case_1600 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  T_StoreWF_456 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'case_1600 v0 v1 v2 v3 v4 v5 v6
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v7 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                          (coe v5)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v8
               -> case coe v8 of
                    0 -> coe
                           d_wf'45'trace_1588 (coe v0) (coe v2) (coe v4) (coe v5) (coe v6)
                    _ -> coe
                           d_wf'45'trace_1588 (coe v0) (coe v3) (coe v4) (coe v5) (coe v6)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v8 v9 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                          (coe v5)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                          (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                   (coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.FlatWF
d_FlatWF_1996 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_FlatWF_1996 = erased
-- Once.CCC.Machine.FlatStoreWF.wf-jump
d_wf'45'jump_2004 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_StoreWF_456 -> T_StoreWF_456
d_wf'45'jump_2004 ~v0 v1 ~v2 v3 = du_wf'45'jump_2004 v1 v3
du_wf'45'jump_2004 ::
  Maybe Integer -> T_StoreWF_456 -> T_StoreWF_456
du_wf'45'jump_2004 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatStoreWF.wf-branch
d_wf'45'branch_2024 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_StoreWF_456 -> T_StoreWF_456
d_wf'45'branch_2024 v0 v1 v2 v3 ~v4 v5
  = du_wf'45'branch_2024 v0 v1 v2 v3 v5
du_wf'45'branch_2024 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_StoreWF_456 -> T_StoreWF_456
du_wf'45'branch_2024 v0 v1 v2 v3 v4
  = if coe v1
      then coe
             du_wf'45'jump_2004
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_142 (coe v0)
                (coe v3) (coe v2))
             (coe v4)
      else coe v4
-- Once.CCC.Machine.FlatStoreWF.flat-wf-step
d_flat'45'wf'45'step_2048 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_StoreWF_456 -> T_StoreWF_456
d_flat'45'wf'45'step_2048 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2244
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2246
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2248
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2250
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2252 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2254 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2256
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2258
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2260 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2262 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2264 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2266 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2268 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2270 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2272
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2274
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2276 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2278 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2280 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2282 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2288 v5 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2292 v5 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2294 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2296
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2298 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2300 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2302 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2304 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2306 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2308 v5
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2230 v6 -> coe v4
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2232 v6
               -> coe
                    du_wf'45'jump_2004
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_142 (coe v0)
                       (coe v2) (coe v6))
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2234 v6
               -> coe
                    du_wf'45'branch_2024 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_78
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552
                             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3)))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)))
                    (coe v6) (coe v2) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2236 v6
               -> coe
                    du_wf'45'branch_2024 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_80
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_92
                          (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))))
                    (coe v6) (coe v2) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2310 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1580 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
