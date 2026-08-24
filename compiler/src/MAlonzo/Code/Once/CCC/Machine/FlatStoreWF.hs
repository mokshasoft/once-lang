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
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Machine.FlatStoreWF._.readLoc
d_readLoc_26 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_26 ~v0 = du_readLoc_26
du_readLoc_26 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_26
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644
-- Once.CCC.Machine.FlatStoreWF._.writeHeapMem-aux
d_writeHeapMem'45'aux_32 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_writeHeapMem'45'aux_32 ~v0 = du_writeHeapMem'45'aux_32
du_writeHeapMem'45'aux_32 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_writeHeapMem'45'aux_32 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem'45'aux_776 v2
      v3 v4
-- Once.CCC.Machine.FlatStoreWF._.writeLoc
d_writeLoc_34 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLoc_34 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_810 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.writeLocToHeap
d_writeLocToHeap_50 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLocToHeap_50 ~v0 = du_writeLocToHeap_50
du_writeLocToHeap_50 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_writeLocToHeap_50
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_802
-- Once.CCC.Machine.FlatStoreWF._.writeLocToStack
d_writeLocToStack_52 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLocToStack_52 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLocToStack_792 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.writeStackMem-aux
d_writeStackMem'45'aux_56 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_writeStackMem'45'aux_56 ~v0 = du_writeStackMem'45'aux_56
du_writeStackMem'45'aux_56 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_writeStackMem'45'aux_56 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeStackMem'45'aux_664 v4
      v5 v6 v7
-- Once.CCC.Machine.FlatStoreWF._.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_62 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_exec'45'lea'45'indexed'45'via_62 ~v0
  = du_exec'45'lea'45'indexed'45'via_62
du_exec'45'lea'45'indexed'45'via_62 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_exec'45'lea'45'indexed'45'via_62
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'lea'45'indexed'45'via_1490
-- Once.CCC.Machine.FlatStoreWF._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_68 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_exec'45'load'45'suc'45'via'45'resolved_68 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_68
du_exec'45'load'45'suc'45'via'45'resolved_68 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_exec'45'load'45'suc'45'via'45'resolved_68
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'suc'45'via'45'resolved_1502
-- Once.CCC.Machine.FlatStoreWF._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_70 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_exec'45'load'45'via'45'resolved_70 ~v0
  = du_exec'45'load'45'via'45'resolved_70
du_exec'45'load'45'via'45'resolved_70 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_exec'45'load'45'via'45'resolved_70
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'via'45'resolved_1464
-- Once.CCC.Machine.FlatStoreWF._.exec-load-with-value
d_exec'45'load'45'with'45'value_72 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_exec'45'load'45'with'45'value_72 ~v0
  = du_exec'45'load'45'with'45'value_72
du_exec'45'load'45'with'45'value_72 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_exec'45'load'45'with'45'value_72
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'with'45'value_1452
-- Once.CCC.Machine.FlatStoreWF._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_74 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_exec'45'store'45'suc'45'via'45'resolved_74 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'suc'45'via'45'resolved_1514
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_76 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_exec'45'store'45'via'45'resolved_76 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'via'45'resolved_1476
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.slot-base
d_slot'45'base_80 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_80 ~v0 = du_slot'45'base_80
du_slot'45'base_80 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_80
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_slot'45'base_1486
-- Once.CCC.Machine.FlatStoreWF._.BodyRunner
d_BodyRunner_86 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_BodyRunner_86 = erased
-- Once.CCC.Machine.FlatStoreWF._.exec-abstract
d_exec'45'abstract_92 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_92 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2814
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.exec-case-dispatch
d_exec'45'case'45'dispatch_96 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'case'45'dispatch_96 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'case'45'dispatch_2820
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_102 ~v0
  = du_exec'45'load'45'from'45'slot'45'with'45'value_102
du_exec'45'load'45'from'45'slot'45'with'45'value_102 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_102
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'from'45'slot'45'with'45'value_2500
-- Once.CCC.Machine.FlatStoreWF._.exec-loop-run
d_exec'45'loop'45'run_106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop'45'run_106 ~v0 = du_exec'45'loop'45'run_106
du_exec'45'loop'45'run_106 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'loop'45'run_106
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'loop'45'run_2748
-- Once.CCC.Machine.FlatStoreWF._.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_112 ~v0
  = du_exec'45'restore'45'input'45'with'45'value_112
du_exec'45'restore'45'input'45'with'45'value_112 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_112
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'restore'45'input'45'with'45'value_2512
-- Once.CCC.Machine.FlatStoreWF._.exec-sigop-output
d_exec'45'sigop'45'output_118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output_118 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output_2698
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output'45'of_120 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output'45'of_2688
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.exec-trace
d_exec'45'trace_122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_122 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2816 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.loop-reanchor-alloc
d_loop'45'reanchor'45'alloc_150 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_loop'45'reanchor'45'alloc_150 ~v0
  = du_loop'45'reanchor'45'alloc_150
du_loop'45'reanchor'45'alloc_150 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_loop'45'reanchor'45'alloc_150
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'alloc_2742
-- Once.CCC.Machine.FlatStoreWF._.loop-reanchor-loc
d_loop'45'reanchor'45'loc_152 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_loop'45'reanchor'45'loc_152 ~v0 = du_loop'45'reanchor'45'loc_152
du_loop'45'reanchor'45'loc_152 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_loop'45'reanchor'45'loc_152
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'loc_2736
-- Once.CCC.Machine.FlatStoreWF._.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'aux_154 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'aux_2652
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_156 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'val_156 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_pure'45'sigop'45'out'45'val_2636
      (coe v0) v2 v3 v4 v5
-- Once.CCC.Machine.FlatStoreWF._.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_structured'45'pure'45'sigop'45'output_168 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_structured'45'pure'45'sigop'45'output_2624
      v0
-- Once.CCC.Machine.FlatStoreWF._.CallPost
d_CallPost_174 a0 a1 a2 = ()
-- Once.CCC.Machine.FlatStoreWF._.FlatState
d_FlatState_176 a0 = ()
-- Once.CCC.Machine.FlatStoreWF._.do-branch
d_do'45'branch_192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'branch_192 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'branch_516 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.do-call
d_do'45'call_194 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call_194 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call_918 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.do-jump
d_do'45'jump_202 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'jump_202 ~v0 = du_do'45'jump_202
du_do'45'jump_202 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'jump_202
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_508
-- Once.CCC.Machine.FlatStoreWF._.do-ret
d_do'45'ret_204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'ret_204 ~v0 = du_do'45'ret_204
du_do'45'ret_204 ::
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'ret_204
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'ret_718
-- Once.CCC.Machine.FlatStoreWF._.do-thunk
d_do'45'thunk_218 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'thunk_218 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'thunk_852 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.flat-exec-instr
d_flat'45'exec'45'instr_272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_272 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1080
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.FlatState.falloc
d_falloc_370 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_falloc_370 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.FlatState.fclosure
d_fclosure_372 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_372 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.FlatState.flink
d_flink_374 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_374 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.FlatState.floc
d_floc_376 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_376 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.FlatState.fpc
d_fpc_378 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_378 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.FlatState.fret
d_fret_380 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_380 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Machine.FlatStoreWF.loc-below
d_loc'45'below_390 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_loc'45'below_390 = erased
-- Once.CCC.Machine.FlatStoreWF.sv-below
d_sv'45'below_398 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_sv'45'below_398 = erased
-- Once.CCC.Machine.FlatStoreWF.svm-below
d_svm'45'below_410 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_svm'45'below_410 = erased
-- Once.CCC.Machine.FlatStoreWF.mloc-below
d_mloc'45'below_418 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  ()
d_mloc'45'below_418 = erased
-- Once.CCC.Machine.FlatStoreWF.loc-mono
d_loc'45'mono_432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_loc'45'mono_432 ~v0 ~v1 ~v2 v3 v4 v5
  = du_loc'45'mono_432 v3 v4 v5
du_loc'45'mono_432 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_loc'45'mono_432 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v2)
             (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.sv-mono
d_sv'45'mono_446 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_sv'45'mono_446 ~v0 ~v1 ~v2 v3 v4 v5 = du_sv'45'mono_446 v3 v4 v5
du_sv'45'mono_446 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_sv'45'mono_446 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v3
        -> coe du_loc'45'mono_432 (coe v3) (coe v1) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.svm-mono
d_svm'45'mono_460 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_svm'45'mono_460 ~v0 ~v1 ~v2 v3 v4 v5
  = du_svm'45'mono_460 v3 v4 v5
du_svm'45'mono_460 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_svm'45'mono_460 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe du_sv'45'mono_446 (coe v3) (coe v1) (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.sv-as-loc-below
d_sv'45'as'45'loc'45'below_472 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny
d_sv'45'as'45'loc'45'below_472 ~v0 ~v1 v2 v3
  = du_sv'45'as'45'loc'45'below_472 v2 v3
du_sv'45'as'45'loc'45'below_472 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny
du_sv'45'as'45'loc'45'below_472 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v2
        -> case coe v2 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.slot-base-below
d_slot'45'base'45'below_498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny
d_slot'45'base'45'below_498 ~v0 ~v1 v2 v3
  = du_slot'45'base'45'below_498 v2 v3
du_slot'45'base'45'below_498 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny
du_slot'45'base'45'below_498 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe du_sv'45'as'45'loc'45'below_472 (coe v2) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.sucLoc-below
d_sucLoc'45'below_512 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> AgdaAny
d_sucLoc'45'below_512 ~v0 ~v1 v2 v3 = du_sucLoc'45'below_512 v2 v3
du_sucLoc'45'below_512 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> AgdaAny
du_sucLoc'45'below_512 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe seq (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.offsetLoc-below
d_offsetLoc'45'below_534 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> AgdaAny -> AgdaAny
d_offsetLoc'45'below_534 ~v0 ~v1 v2 ~v3 v4
  = du_offsetLoc'45'below_534 v2 v4
du_offsetLoc'45'below_534 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> AgdaAny
du_offsetLoc'45'below_534 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe seq (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.sv-succ-below
d_sv'45'succ'45'below_558 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
d_sv'45'succ'45'below_558 ~v0 ~v1 v2
  = du_sv'45'succ'45'below_558 v2
du_sv'45'succ'45'below_558 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
du_sv'45'succ'45'below_558 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatStoreWF.sv-pred-below
d_sv'45'pred'45'below_572 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
d_sv'45'pred'45'below_572 ~v0 ~v1 v2
  = du_sv'45'pred'45'below_572 v2
du_sv'45'pred'45'below_572 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
du_sv'45'pred'45'below_572 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v1
        -> coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.StoreWF
d_StoreWF_588 a0 a1 a2 = ()
data T_StoreWF_588
  = C_constructor_630 (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
                       AgdaAny)
                      (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny)
                      (AgdaAny -> Integer -> AgdaAny)
-- Once.CCC.Machine.FlatStoreWF.StoreWF.wf-regs
d_wf'45'regs_614 ::
  T_StoreWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
d_wf'45'regs_614 v0
  = case coe v0 of
      C_constructor_630 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.StoreWF.wf-heap
d_wf'45'heap_618 ::
  T_StoreWF_588 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny
d_wf'45'heap_618 v0
  = case coe v0 of
      C_constructor_630 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.StoreWF.wf-stack
d_wf'45'stack_624 :: T_StoreWF_588 -> AgdaAny -> Integer -> AgdaAny
d_wf'45'stack_624 v0
  = case coe v0 of
      C_constructor_630 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.StoreWF.wf-fresh
d_wf'45'fresh_628 ::
  T_StoreWF_588 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wf'45'fresh_628 = erased
-- Once.CCC.Machine.FlatStoreWF.rw-below
d_rw'45'below_642 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_rw'45'below_642 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du_rw'45'below_642 v3 v4 v6 v7
du_rw'45'below_642 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_rw'45'below_642 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56 -> coe v2
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62 -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58 -> coe v2
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62 -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60 -> coe v2
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62 -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62 -> coe v2
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-write-reg
d_wf'45'write'45'reg_780 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_588 -> AgdaAny -> T_StoreWF_588
d_wf'45'write'45'reg_780 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_wf'45'write'45'reg_780 v3 v5 v6
du_wf'45'write'45'reg_780 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  T_StoreWF_588 -> AgdaAny -> T_StoreWF_588
du_wf'45'write'45'reg_780 v0 v1 v2
  = coe
      C_constructor_630
      (\ v3 ->
         coe
           du_rw'45'below_642 (coe v0) (coe v3) (coe v2)
           (coe d_wf'45'regs_614 v1 v3))
      (d_wf'45'heap_618 (coe v1)) (d_wf'45'stack_624 (coe v1))
-- Once.CCC.Machine.FlatStoreWF.wf-halt
d_wf'45'halt_800 :: T_StoreWF_588 -> T_StoreWF_588
d_wf'45'halt_800 v0 = coe v0
-- Once.CCC.Machine.FlatStoreWF.wf-write-reg-halt
d_wf'45'write'45'reg'45'halt_814 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Bool -> T_StoreWF_588 -> AgdaAny -> T_StoreWF_588
d_wf'45'write'45'reg'45'halt_814 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du_wf'45'write'45'reg'45'halt_814 v3 v6 v7
du_wf'45'write'45'reg'45'halt_814 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  T_StoreWF_588 -> AgdaAny -> T_StoreWF_588
du_wf'45'write'45'reg'45'halt_814 v0 v1 v2
  = coe
      C_constructor_630
      (\ v3 ->
         coe
           du_rw'45'below_642 (coe v0) (coe v3) (coe v2)
           (coe d_wf'45'regs_614 v1 v3))
      (d_wf'45'heap_618 (coe v1)) (d_wf'45'stack_624 (coe v1))
-- Once.CCC.Machine.FlatStoreWF.wsm-below
d_wsm'45'below_850 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_wsm'45'below_850 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 v10 v11
  = du_wsm'45'below_850 v6 v7 v10 v11
du_wsm'45'below_850 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_wsm'45'below_850 v0 v1 v2 v3
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
d_wf'45'write'45'stack_886 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_588 -> AgdaAny -> T_StoreWF_588
d_wf'45'write'45'stack_886 v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du_wf'45'write'45'stack_886 v0 v3 v4 v6 v7
du_wf'45'write'45'stack_886 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> T_StoreWF_588 -> AgdaAny -> T_StoreWF_588
du_wf'45'write'45'stack_886 v0 v1 v2 v3 v4
  = coe
      C_constructor_630 (d_wf'45'regs_614 (coe v3))
      (d_wf'45'heap_618 (coe v3))
      (\ v5 v6 ->
         coe
           du_wsm'45'below_850
           (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__88 v0 v1 v5)
           (coe
              MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v2) (coe v6))
           (coe d_wf'45'stack_624 v3 v5 v6) (coe v4))
-- Once.CCC.Machine.FlatStoreWF.whm-below
d_whm'45'below_918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_whm'45'below_918 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8
  = du_whm'45'below_918 v4 v7 v8
du_whm'45'below_918 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_whm'45'below_918 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe seq (coe v4) (coe v2)
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.whm-fresh
d_whm'45'fresh_948 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_whm'45'fresh_948 = erased
-- Once.CCC.Machine.FlatStoreWF.wf-write-heap
d_wf'45'write'45'heap_978 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_588 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> T_StoreWF_588
d_wf'45'write'45'heap_978 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7
  = du_wf'45'write'45'heap_978 v3 v5 v7
du_wf'45'write'45'heap_978 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoreWF_588 -> AgdaAny -> T_StoreWF_588
du_wf'45'write'45'heap_978 v0 v1 v2
  = coe
      C_constructor_630 (d_wf'45'regs_614 (coe v1))
      (\ v3 ->
         coe
           du_whm'45'below_918
           (coe
              MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__80 (coe v0)
              (coe v3))
           (coe d_wf'45'heap_618 v1 v3) (coe v2))
      (d_wf'45'stack_624 (coe v1))
-- Once.CCC.Machine.FlatStoreWF.wf-write-loc
d_wf'45'write'45'loc_1008 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_588 -> AgdaAny -> AgdaAny -> T_StoreWF_588
d_wf'45'write'45'loc_1008 v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_wf'45'write'45'loc_1008 v0 v3 v4 v5 v7
du_wf'45'write'45'loc_1008 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_588 -> AgdaAny -> T_StoreWF_588
du_wf'45'write'45'loc_1008 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v5 v6
        -> coe
             du_wf'45'write'45'stack_886 (coe v0) (coe v5) (coe v6) (coe v3)
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v5
        -> case coe v2 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v6
               -> coe
                    seq (coe v6)
                    (coe du_wf'45'write'45'heap_978 (coe v5) (coe v3) (coe v4))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v6
               -> coe du_wf'45'write'45'heap_978 (coe v5) (coe v3) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v6 v7 v8
               -> coe du_wf'45'write'45'heap_978 (coe v5) (coe v3) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v6
               -> coe du_wf'45'write'45'heap_978 (coe v5) (coe v3) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.readLoc-below
d_readLoc'45'below_1080 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_588 -> AgdaAny
d_readLoc'45'below_1080 ~v0 ~v1 ~v2 v3 v4
  = du_readLoc'45'below_1080 v3 v4
du_readLoc'45'below_1080 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_588 -> AgdaAny
du_readLoc'45'below_1080 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe d_wf'45'stack_624 v1 v2 v3
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe d_wf'45'heap_618 v1 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-load-value
d_wf'45'load'45'value_1100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_588 -> AgdaAny -> T_StoreWF_588
d_wf'45'load'45'value_1100 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_wf'45'load'45'value_1100 v3 v4 v5 v6
du_wf'45'load'45'value_1100 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_588 -> AgdaAny -> T_StoreWF_588
du_wf'45'load'45'value_1100 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe du_wf'45'write'45'reg_780 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-load-resolved
d_wf'45'load'45'resolved_1122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_588 -> AgdaAny -> T_StoreWF_588
d_wf'45'load'45'resolved_1122 ~v0 ~v1 v2 v3 v4 v5 ~v6
  = du_wf'45'load'45'resolved_1122 v2 v3 v4 v5
du_wf'45'load'45'resolved_1122 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_588 -> T_StoreWF_588
du_wf'45'load'45'resolved_1122 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_wf'45'load'45'value_1100 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644 (coe v0)
                (coe v4))
             (coe v3) (coe du_readLoc'45'below_1080 (coe v4) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-load-suc-resolved
d_wf'45'load'45'suc'45'resolved_1142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_588 -> AgdaAny -> T_StoreWF_588
d_wf'45'load'45'suc'45'resolved_1142 ~v0 ~v1 v2 v3 v4 v5 ~v6
  = du_wf'45'load'45'suc'45'resolved_1142 v2 v3 v4 v5
du_wf'45'load'45'suc'45'resolved_1142 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_588 -> T_StoreWF_588
du_wf'45'load'45'suc'45'resolved_1142 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_wf'45'load'45'value_1100 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644 (coe v0)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v4)))
             (coe v3)
             (coe
                du_readLoc'45'below_1080
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v4))
                (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-store-resolved
d_wf'45'store'45'resolved_1168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_588 -> AgdaAny -> AgdaAny -> T_StoreWF_588
d_wf'45'store'45'resolved_1168 v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_wf'45'store'45'resolved_1168 v0 v3 v4 v5 v7
du_wf'45'store'45'resolved_1168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_588 -> AgdaAny -> T_StoreWF_588
du_wf'45'store'45'resolved_1168 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_wf'45'write'45'loc_1008 (coe v0) (coe v5) (coe v2) (coe v3)
             (coe v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-store-suc-resolved
d_wf'45'store'45'suc'45'resolved_1192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_588 -> AgdaAny -> AgdaAny -> T_StoreWF_588
d_wf'45'store'45'suc'45'resolved_1192 v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_wf'45'store'45'suc'45'resolved_1192 v0 v3 v4 v5 v7
du_wf'45'store'45'suc'45'resolved_1192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_588 -> AgdaAny -> T_StoreWF_588
du_wf'45'store'45'suc'45'resolved_1192 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_wf'45'write'45'loc_1008 (coe v0)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v5))
             (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-lea-indexed
d_wf'45'lea'45'indexed_1220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_StoreWF_588 -> AgdaAny -> T_StoreWF_588
d_wf'45'lea'45'indexed_1220 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_wf'45'lea'45'indexed_1220 v3 v5 v6
du_wf'45'lea'45'indexed_1220 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_588 -> AgdaAny -> T_StoreWF_588
du_wf'45'lea'45'indexed_1220 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_wf'45'write'45'reg_780
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v1)
             (coe du_offsetLoc'45'below_534 (coe v3) (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-slot-load
d_wf'45'slot'45'load_1246 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_588 -> AgdaAny -> T_StoreWF_588
d_wf'45'slot'45'load_1246 ~v0 ~v1 ~v2 = du_wf'45'slot'45'load_1246
du_wf'45'slot'45'load_1246 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_588 -> AgdaAny -> T_StoreWF_588
du_wf'45'slot'45'load_1246 = coe du_wf'45'load'45'value_1100
-- Once.CCC.Machine.FlatStoreWF.structured-pure-sigop-below
d_structured'45'pure'45'sigop'45'below_1258
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.FlatStoreWF.structured-pure-sigop-below"
-- Once.CCC.Machine.FlatStoreWF.pure-out-val-below
d_pure'45'out'45'val'45'below_1272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 -> Maybe AgdaAny -> AgdaAny
d_pure'45'out'45'val'45'below_1272 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_pure'45'out'45'val'45'below_1272 v6
du_pure'45'out'45'val'45'below_1272 :: Maybe AgdaAny -> AgdaAny
du_pure'45'out'45'val'45'below_1272 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatStoreWF.sigop-output-below
d_sigop'45'output'45'below_1298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> AgdaAny
d_sigop'45'output'45'below_1298 v0 v1 v2 v3 v4 v5
  = coe
      d_go_1328 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_216 (coe v4))
-- Once.CCC.Machine.FlatStoreWF._.aux
d_aux_1318 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
d_aux_1318 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> coe
                    du_pure'45'out'45'val'45'below_1272
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2594 (coe v2)
                       (coe v9) (coe v5))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    du_pure'45'out'45'val'45'below_1272
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg'45'typed_2588
                       (coe v2)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v5))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             d_structured'45'pure'45'sigop'45'below_1258 v0 v1 v2 v3 v4 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF._.go
d_go_1328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 -> AgdaAny
d_go_1328 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_124
        -> coe
             d_aux_1318 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_204 (coe v3))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1360
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v5))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
      MAlonzo.Code.Once.SigOp.Info.C_Emits_126
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.SigOp.Info.C_Halts_128
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-slot-load-out
d_wf'45'slot'45'load'45'out_1336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_StoreWF_588 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'slot'45'load'45'out_1336 ~v0 v1 ~v2 v3 v4 v5
  = du_wf'45'slot'45'load'45'out_1336 v1 v3 v4 v5
du_wf'45'slot'45'load'45'out_1336 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_StoreWF_588 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf'45'slot'45'load'45'out_1336 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_780
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v2)
                (coe v3))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v1)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-slot-load-in1
d_wf'45'slot'45'load'45'in1_1360 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_StoreWF_588 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'slot'45'load'45'in1_1360 ~v0 v1 ~v2 v3 v4 v5
  = du_wf'45'slot'45'load'45'in1_1360 v1 v3 v4 v5
du_wf'45'slot'45'load'45'in1_1360 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_StoreWF_588 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf'45'slot'45'load'45'in1_1360 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_780
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v2)
                (coe v3))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v1)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.Preserves
d_Preserves_1382 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_Preserves_1382 = erased
-- Once.CCC.Machine.FlatStoreWF.BodyPreserves
d_BodyPreserves_1392 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  ()
d_BodyPreserves_1392 = erased
-- Once.CCC.Machine.FlatStoreWF.wf-loop-run
d_wf'45'loop'45'run_1408 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   T_StoreWF_588 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_588 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'loop'45'run_1408 v0 v1 v2 v3 v4 v5 v6
  = case coe v2 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v4)))
      _ -> let v7 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (let v8
                    = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_420 (coe v3) in
              coe
                (if coe v8
                   then coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                                (coe v4)))
                   else (let v9
                               = MAlonzo.Code.Once.CCC.Machine.SMCore.d_scratch_140
                                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v3)) in
                         coe
                           (case coe v9 of
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v10
                                -> coe
                                     d_wf'45'loop'45'run'45'go_1418 (coe v0) (coe v1) (coe v7)
                                     (coe v3) (coe v4) (coe v5) (coe v6)
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v10
                                -> case coe v10 of
                                     0 -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                            (coe
                                               MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                                                  (coe v4)))
                                     _ -> coe
                                            d_wf'45'loop'45'run'45'go_1418 (coe v0) (coe v1)
                                            (coe v7) (coe v3) (coe v4) (coe v5) (coe v6)
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v10 v11 v12
                                -> coe
                                     d_wf'45'loop'45'run'45'go_1418 (coe v0) (coe v1) (coe v7)
                                     (coe v3) (coe v4) (coe v5) (coe v6)
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v10
                                -> coe
                                     d_wf'45'loop'45'run'45'go_1418 (coe v0) (coe v1) (coe v7)
                                     (coe v3) (coe v4) (coe v5) (coe v6)
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Machine.FlatStoreWF.wf-loop-run-go
d_wf'45'loop'45'run'45'go_1418 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   T_StoreWF_588 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_588 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'loop'45'run'45'go_1418 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_rec_1564 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v6)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe du_step_1552 (coe v3) (coe v4) (coe v5) (coe v6)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_rec_1564 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6))))
-- Once.CCC.Machine.FlatStoreWF._.step
d_step_1552 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   T_StoreWF_588 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_588 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_1552 ~v0 ~v1 ~v2 v3 v4 v5 v6 = du_step_1552 v3 v4 v5 v6
du_step_1552 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   T_StoreWF_588 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_588 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_1552 v0 v1 v2 v3 = coe v2 v0 v1 v3
-- Once.CCC.Machine.FlatStoreWF._.ls''
d_ls''''_1554 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   T_StoreWF_588 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_ls''''_1554 ~v0 v1 ~v2 v3 v4 ~v5 ~v6 = du_ls''''_1554 v1 v3 v4
du_ls''''_1554 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_ls''''_1554 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'loc_2736
      (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0 v1 v2))
-- Once.CCC.Machine.FlatStoreWF._.al''
d_al''''_1556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   T_StoreWF_588 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_al''''_1556 ~v0 v1 ~v2 v3 v4 ~v5 ~v6 = du_al''''_1556 v1 v3 v4
du_al''''_1556 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_al''''_1556 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'alloc_2742
      (coe v2)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0 v1 v2))
-- Once.CCC.Machine.FlatStoreWF._.wf''
d_wf''''_1558 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   T_StoreWF_588 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_588 -> T_StoreWF_588
d_wf''''_1558 ~v0 ~v1 ~v2 v3 v4 v5 v6 = du_wf''''_1558 v3 v4 v5 v6
du_wf''''_1558 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   T_StoreWF_588 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_588 -> T_StoreWF_588
du_wf''''_1558 v0 v1 v2 v3
  = coe
      C_constructor_630
      (d_wf'45'regs_614
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe du_step_1552 (coe v0) (coe v1) (coe v2) (coe v3))))
      (d_wf'45'heap_618
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe du_step_1552 (coe v0) (coe v1) (coe v2) (coe v3))))
      (\ v4 v5 ->
         coe
           du_svm'45'mono_460
           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_416 v0 v4 v5)
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
              (coe du_step_1552 (coe v0) (coe v1) (coe v2) (coe v3)))
           (coe d_wf'45'stack_624 v3 v4 v5))
-- Once.CCC.Machine.FlatStoreWF._.rec
d_rec_1564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   T_StoreWF_588 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_588 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rec_1564 v0 v1 v2 v3 v4 v5 v6
  = coe
      d_wf'45'loop'45'run_1408 (coe v0) (coe v1) (coe v2)
      (coe du_ls''''_1554 (coe v1) (coe v3) (coe v4))
      (coe du_al''''_1556 (coe v1) (coe v3) (coe v4)) (coe v5)
      (coe du_wf''''_1558 (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.CCC.Machine.FlatStoreWF.wf-abstract
d_wf'45'abstract_1572 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_StoreWF_588 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'abstract_1572 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_780
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v4)
                (coe
                   d_wf'45'regs_614 v4
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_780
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v4)
                (coe
                   d_wf'45'regs_614 v4
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'load'45'resolved_1122 (coe v2)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1360
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v2))
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                (coe v4))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'load'45'suc'45'resolved_1142 (coe v2)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1360
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v2))
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                (coe v4))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228 v5
        -> coe
             du_wf'45'slot'45'load'45'out_1336
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                      (coe v3))
                   (coe v5)))
             (coe v3) (coe v4)
             (coe
                du_readLoc'45'below_1080
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                      (coe v3))
                   (coe v5))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'loc_1008 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                      (coe v3))
                   (coe v5))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
                (coe v4)
                (coe
                   d_wf'45'regs_614 v4
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'store'45'resolved_1168 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1360
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v2))
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
                (coe v4)
                (coe
                   d_wf'45'regs_614 v4
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'store'45'suc'45'resolved_1192 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1360
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v2))
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
                (coe v4)
                (coe
                   d_wf'45'regs_614 v4
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2236 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_780
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v4)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2238 v5
        -> coe
             du_wf'45'slot'45'load'45'in1_1360
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                      (coe v3))
                   (coe v5)))
             (coe v3) (coe v4)
             (coe
                du_readLoc'45'below_1080
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                      (coe v3))
                   (coe v5))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2240 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2242 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2244 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2246 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2248
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2250
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2252 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2254 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'loc_1008 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                      (coe v3))
                   (coe v5))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
                (coe v4)
                (coe
                   d_wf'45'regs_614 v4
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2256 v5
        -> coe
             du_wf'45'slot'45'load'45'out_1336
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                      (coe v3))
                   (coe v5)))
             (coe v3) (coe v4)
             (coe
                du_readLoc'45'below_1080
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                      (coe v3))
                   (coe v5))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2258 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2264 v5 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg'45'halt_814
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v4)
                (coe
                   d_sigop'45'output'45'below_1298 (coe v0)
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                      (coe v3))
                   (coe v5) (coe v6) (coe v7) (coe v2)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2270 v5 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_780
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v4)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2272 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_780
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v4)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2274
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_780
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v4)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2278 v5 v6
        -> coe
             d_wf'45'case_1592 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_case'45'tag'45'at_2720
                (coe v2))
             (coe v5) (coe v6) (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_constructor_630
                (\ v6 ->
                   coe
                     du_rw'45'below_642
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v6)
                     (coe
                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                        (coe
                           addInt (coe (1 :: Integer))
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                              (coe v3))))
                     (coe
                        du_sv'45'mono_446
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v2))
                           (coe v6))
                        (coe
                           MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                              (coe v3)))
                        (coe d_wf'45'regs_614 v4 v6)))
                (\ v6 ->
                   coe
                     du_svm'45'mono_460
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_418 v2 v6)
                     (coe
                        MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                           (coe v3)))
                     (coe d_wf'45'heap_618 v4 v6))
                (\ v6 v7 ->
                   coe
                     du_svm'45'mono_460
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_416 v2 v6 v7)
                     (coe
                        MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                           (coe v3)))
                     (coe d_wf'45'stack_624 v4 v6 v7)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2282 v5
        -> coe
             d_wf'45'loop'45'run_1408 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2816 (coe v0)
                (coe v5))
             (coe (1000000 :: Integer)) (coe v2) (coe v3)
             (coe d_wf'45'trace_1580 (coe v0) (coe v5)) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284 v5
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_370
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_wf'45'write'45'reg_780
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60) (coe v4)
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                          (coe v3)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_372
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_wf'45'write'45'reg_780
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60) (coe v4)
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                          (coe v3)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_wf'45'write'45'reg_780
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60) (coe v4)
                       (coe
                          du_sv'45'pred'45'below_572
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v2))
                             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60))))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                          (coe v3)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_wf'45'write'45'reg_780
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60) (coe v4)
                       (coe
                          d_wf'45'regs_614 v4
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62)))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                          (coe v3)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_wf'45'write'45'reg_780
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62) (coe v4)
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                          (coe v3)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_wf'45'write'45'reg_780
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62) (coe v4)
                       (coe
                          du_sv'45'succ'45'below_558
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v2))
                             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62))))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                          (coe v3)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2288 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'lea'45'indexed_1220
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_slot'45'base_1486
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644 (coe v2)
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                            (coe v3))
                         (coe v5))))
                (coe v4)
                (coe
                   du_slot'45'base'45'below_498
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644 (coe v2)
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                            (coe v3))
                         (coe v5)))
                   (coe
                      du_readLoc'45'below_1080
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                            (coe v3))
                         (coe v5))
                      (coe v4))))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-trace
d_wf'45'trace_1580 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_StoreWF_588 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'trace_1580 v0 v1 v2 v3 v4
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      (:) v5 v6
        -> let v7
                 = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_420 (coe v2) in
           coe
             (if coe v7
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                             (coe v3)))
                else coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_wf'45'trace_1580 (coe v0) (coe v6)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2814
                                   (coe v0) (coe v5) (coe v2) (coe v3)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2814
                                   (coe v0) (coe v5) (coe v2) (coe v3)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   d_wf'45'abstract_1572 (coe v0) (coe v5) (coe v2) (coe v3)
                                   (coe v4)))))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_wf'45'abstract_1572 (coe v0) (coe v5) (coe v2) (coe v3)
                                (coe v4)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_wf'45'trace_1580 (coe v0) (coe v6)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2814
                                      (coe v0) (coe v5) (coe v2) (coe v3)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2814
                                      (coe v0) (coe v5) (coe v2) (coe v3)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_wf'45'abstract_1572 (coe v0) (coe v5) (coe v2) (coe v3)
                                      (coe v4)))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-case
d_wf'45'case_1592 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_StoreWF_588 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'case_1592 v0 v1 v2 v3 v4 v5 v6
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v7 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                          (coe v5)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v8
               -> case coe v8 of
                    0 -> coe
                           d_wf'45'trace_1580 (coe v0) (coe v2) (coe v4) (coe v5) (coe v6)
                    _ -> coe
                           d_wf'45'trace_1580 (coe v0) (coe v3) (coe v4) (coe v5) (coe v6)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v8 v9 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                          (coe v5)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                          (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.FlatWF
d_FlatWF_1976 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_FlatWF_1976 = erased
-- Once.CCC.Machine.FlatStoreWF.wf-jump
d_wf'45'jump_1984 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_StoreWF_588 -> T_StoreWF_588
d_wf'45'jump_1984 ~v0 v1 ~v2 v3 = du_wf'45'jump_1984 v1 v3
du_wf'45'jump_1984 ::
  Maybe Integer -> T_StoreWF_588 -> T_StoreWF_588
du_wf'45'jump_1984 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatStoreWF.wf-branch
d_wf'45'branch_2004 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_StoreWF_588 -> T_StoreWF_588
d_wf'45'branch_2004 v0 v1 v2 v3 ~v4 v5
  = du_wf'45'branch_2004 v0 v1 v2 v3 v5
du_wf'45'branch_2004 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_StoreWF_588 -> T_StoreWF_588
du_wf'45'branch_2004 v0 v1 v2 v3 v4
  = if coe v1
      then coe
             du_wf'45'jump_1984
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
                (coe v3) (coe v2))
             (coe v4)
      else coe v4
-- Once.CCC.Machine.FlatStoreWF.wf-ret
d_wf'45'ret_2026 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_StoreWF_588 -> T_StoreWF_588
d_wf'45'ret_2026 ~v0 v1 ~v2 v3 = du_wf'45'ret_2026 v1 v3
du_wf'45'ret_2026 :: [Integer] -> T_StoreWF_588 -> T_StoreWF_588
du_wf'45'ret_2026 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatStoreWF.wf-thunk
d_wf'45'thunk_2048 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_StoreWF_588 -> T_StoreWF_588
d_wf'45'thunk_2048 v0 v1 v2 v3
  = coe
      C_constructor_630 (d_wf'45'regs_614 (coe v3))
      (d_wf'45'heap_618 (coe v3))
      (d_cleared_2064 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Machine.FlatStoreWF._.cleared
d_cleared_2064 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_StoreWF_588 -> AgdaAny -> Integer -> AgdaAny
d_cleared_2064 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__88 v0
              (coe
                 MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_106 v0
                 (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v2)))
                 v1)
              v4 in
    coe
      (let v7
             = coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                 (\ v7 ->
                    coe
                      MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                      (coe addInt (coe (1 :: Integer)) (coe v5)))
                 (coe
                    MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                 (coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                    (coe
                       MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                       (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v1))) in
       coe
         (case coe v6 of
            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
              -> if coe v8
                   then coe
                          seq (coe v9)
                          (case coe v7 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                               -> if coe v10
                                    then coe
                                           seq (coe v11) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                    else coe seq (coe v11) (coe d_wf'45'stack_624 v3 v4 v5)
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   else coe seq (coe v9) (coe d_wf'45'stack_624 v3 v4 v5)
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.CCC.Machine.FlatStoreWF.wf-call
d_wf'45'call_2090 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_StoreWF_588 -> T_StoreWF_588
d_wf'45'call_2090 v0 v1 v2 v3
  = coe
      du_go_2102 (coe v3)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_callView_946 (coe v0) (coe v1)
         (coe v2))
-- Once.CCC.Machine.FlatStoreWF._.go
d_go_2102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_StoreWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_928 -> T_StoreWF_588
d_go_2102 ~v0 ~v1 ~v2 v3 v4 = du_go_2102 v3 v4
du_go_2102 ::
  T_StoreWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_928 -> T_StoreWF_588
du_go_2102 v0 v1 = coe seq (coe v1) (coe v0)
-- Once.CCC.Machine.FlatStoreWF.cl-jump
d_cl'45'jump_2126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> AgdaAny
d_cl'45'jump_2126 ~v0 v1 ~v2 v3 = du_cl'45'jump_2126 v1 v3
du_cl'45'jump_2126 :: Maybe Integer -> AgdaAny -> AgdaAny
du_cl'45'jump_2126 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatStoreWF.cl-branch
d_cl'45'branch_2146 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> AgdaAny
d_cl'45'branch_2146 v0 v1 v2 v3 ~v4 v5
  = du_cl'45'branch_2146 v0 v1 v2 v3 v5
du_cl'45'branch_2146 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  AgdaAny -> AgdaAny
du_cl'45'branch_2146 v0 v1 v2 v3 v4
  = if coe v1
      then coe
             du_cl'45'jump_2126
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
                (coe v3) (coe v2))
             (coe v4)
      else coe v4
-- Once.CCC.Machine.FlatStoreWF.cl-ret
d_cl'45'ret_2168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> AgdaAny
d_cl'45'ret_2168 ~v0 v1 ~v2 v3 = du_cl'45'ret_2168 v1 v3
du_cl'45'ret_2168 :: [Integer] -> AgdaAny -> AgdaAny
du_cl'45'ret_2168 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatStoreWF.cl-call
d_cl'45'call_2190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> AgdaAny
d_cl'45'call_2190 v0 v1 v2 v3
  = coe
      du_go_2202 (coe v3)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_callView_946 (coe v0) (coe v1)
         (coe v2))
-- Once.CCC.Machine.FlatStoreWF._.go
d_go_2202 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_928 -> AgdaAny
d_go_2202 ~v0 ~v1 ~v2 v3 v4 = du_go_2202 v3 v4
du_go_2202 ::
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_928 -> AgdaAny
du_go_2202 v0 v1 = coe seq (coe v1) (coe v0)
-- Once.CCC.Machine.FlatStoreWF.cl-step
d_cl'45'step_2228 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_StoreWF_588 -> AgdaAny -> AgdaAny
d_cl'45'step_2228 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228 v6
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230 v6
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2236 v6
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2238 v6
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2240 v6
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2242 v6
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2244 v6
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2246 v6
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2248
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2250
        -> coe d_cl'45'call_2190 (coe v0) (coe v2) (coe v3) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2252 v6
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2254 v6
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2256 v6
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2258 v6
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2264 v6 v7 v8
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2270 v6 v7 v8
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2272 v6
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2274
        -> coe
             d_wf'45'regs_614 v4
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276 v6
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2278 v6 v7
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280 v6
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2282 v6
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284 v6
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286 v6
        -> case coe v6 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206 v7 -> coe v5
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208 v7
               -> coe
                    du_cl'45'jump_2126
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
                       (coe v2) (coe v7))
                    (coe v5)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2210 v7
               -> coe
                    du_cl'45'branch_2146 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_104
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
                             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3)))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60)))
                    (coe v7) (coe v2) (coe v5)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2212 v7
               -> coe
                    du_cl'45'branch_2146 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_106
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_118
                          (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))))
                    (coe v7) (coe v2) (coe v5)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2214 v7 v8
               -> coe v5
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2216 v7
               -> coe
                    du_cl'45'ret_2168
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v3))
                    (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2288 v6
        -> coe
             du_sv'45'mono_446
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1572 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.flat-wf-step
d_flat'45'wf'45'step_2588 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_StoreWF_588 -> T_StoreWF_588
d_flat'45'wf'45'step_2588 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2236 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2238 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2240 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2242 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2244 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2246 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2248
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2250
        -> coe d_wf'45'call_2090 (coe v0) (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2252 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2254 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2256 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2258 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2264 v5 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2270 v5 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2272 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2274
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2278 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2282 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286 v5
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206 v6 -> coe v4
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208 v6
               -> coe
                    du_wf'45'jump_1984
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
                       (coe v2) (coe v6))
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2210 v6
               -> coe
                    du_wf'45'branch_2004 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_104
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
                             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3)))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60)))
                    (coe v6) (coe v2) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2212 v6
               -> coe
                    du_wf'45'branch_2004 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_106
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_118
                          (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))))
                    (coe v6) (coe v2) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2214 v6 v7
               -> coe d_wf'45'thunk_2048 (coe v0) (coe v7) (coe v3) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2216 v6
               -> coe
                    du_wf'45'ret_2026
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v3))
                    (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2288 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1572 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
