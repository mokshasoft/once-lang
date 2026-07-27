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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_20 ~v0 = du_readLoc_20
du_readLoc_20 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_20
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_646
-- Once.CCC.Machine.FlatStoreWF._.writeHeapMem-aux
d_writeHeapMem'45'aux_26 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_writeHeapMem'45'aux_26 ~v0 = du_writeHeapMem'45'aux_26
du_writeHeapMem'45'aux_26 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_writeHeapMem'45'aux_26 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem'45'aux_692 v2
      v3 v4
-- Once.CCC.Machine.FlatStoreWF._.writeLoc
d_writeLoc_28 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_writeLoc_28 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_726 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.writeLocToHeap
d_writeLocToHeap_44 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_writeLocToHeap_44 ~v0 = du_writeLocToHeap_44
du_writeLocToHeap_44 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
du_writeLocToHeap_44
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_718
-- Once.CCC.Machine.FlatStoreWF._.writeLocToStack
d_writeLocToStack_46 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_writeLocToStack_46 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLocToStack_708 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.writeStackMem-aux
d_writeStackMem'45'aux_50 ::
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
d_writeStackMem'45'aux_50 ~v0 = du_writeStackMem'45'aux_50
du_writeStackMem'45'aux_50 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_writeStackMem'45'aux_50 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeStackMem'45'aux_666 v4
      v5 v6 v7
-- Once.CCC.Machine.FlatStoreWF._.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_56 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_exec'45'lea'45'indexed'45'via_56 ~v0
  = du_exec'45'lea'45'indexed'45'via_56
du_exec'45'lea'45'indexed'45'via_56 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
du_exec'45'lea'45'indexed'45'via_56
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'lea'45'indexed'45'via_1358
-- Once.CCC.Machine.FlatStoreWF._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_62 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_exec'45'load'45'suc'45'via'45'resolved_62 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_62
du_exec'45'load'45'suc'45'via'45'resolved_62 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
du_exec'45'load'45'suc'45'via'45'resolved_62
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'suc'45'via'45'resolved_1370
-- Once.CCC.Machine.FlatStoreWF._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_64 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_exec'45'load'45'via'45'resolved_64 ~v0
  = du_exec'45'load'45'via'45'resolved_64
du_exec'45'load'45'via'45'resolved_64 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
du_exec'45'load'45'via'45'resolved_64
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'via'45'resolved_1332
-- Once.CCC.Machine.FlatStoreWF._.exec-load-with-value
d_exec'45'load'45'with'45'value_66 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_exec'45'load'45'with'45'value_66 ~v0
  = du_exec'45'load'45'with'45'value_66
du_exec'45'load'45'with'45'value_66 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
du_exec'45'load'45'with'45'value_66
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'with'45'value_1320
-- Once.CCC.Machine.FlatStoreWF._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_68 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_exec'45'store'45'suc'45'via'45'resolved_68 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'suc'45'via'45'resolved_1382
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_70 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_exec'45'store'45'via'45'resolved_70 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'via'45'resolved_1344
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.slot-base
d_slot'45'base_74 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_74 ~v0 = du_slot'45'base_74
du_slot'45'base_74 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_74
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_slot'45'base_1354
-- Once.CCC.Machine.FlatStoreWF._.exec-abstract
d_exec'45'abstract_84 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_84 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2584
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.exec-case-dispatch
d_exec'45'case'45'dispatch_88 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'case'45'dispatch_88 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'case'45'dispatch_2590
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_94 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_94 ~v0
  = du_exec'45'load'45'from'45'slot'45'with'45'value_94
du_exec'45'load'45'from'45'slot'45'with'45'value_94 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_94
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'from'45'slot'45'with'45'value_2350
-- Once.CCC.Machine.FlatStoreWF._.exec-loop
d_exec'45'loop_96 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop_96 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'loop_2588 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_102 ~v0
  = du_exec'45'restore'45'input'45'with'45'value_102
du_exec'45'restore'45'input'45'with'45'value_102 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_102
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'restore'45'input'45'with'45'value_2362
-- Once.CCC.Machine.FlatStoreWF._.exec-sigop-output
d_exec'45'sigop'45'output_108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output_108 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output_2548
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output'45'of_110 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output'45'of_2538
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.exec-trace
d_exec'45'trace_112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_112 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2586 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_138 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'aux_138 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'aux_2502
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'val_140 ~v0
  = du_pure'45'sigop'45'out'45'val_140
du_pure'45'sigop'45'out'45'val_140 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'out'45'val_140 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_pure'45'sigop'45'out'45'val_2486
      v1 v2 v3 v4
-- Once.CCC.Machine.FlatStoreWF._.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_152 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_structured'45'pure'45'sigop'45'output_152 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_structured'45'pure'45'sigop'45'output_2474
      v0
-- Once.CCC.Machine.FlatStoreWF._.FlatState
d_FlatState_158 a0 = ()
-- Once.CCC.Machine.FlatStoreWF._.do-branch
d_do'45'branch_166 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_do'45'branch_166 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'branch_164 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.do-jump
d_do'45'jump_168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_do'45'jump_168 ~v0 = du_do'45'jump_168
du_do'45'jump_168 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_do'45'jump_168
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_156
-- Once.CCC.Machine.FlatStoreWF._.flat-exec-instr
d_flat'45'exec'45'instr_204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_flat'45'exec'45'instr_204 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_244
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.FlatState.falloc
d_falloc_242 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510
d_falloc_242 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.FlatState.floc
d_floc_244 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_floc_244 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.FlatState.fpc
d_fpc_246 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> Integer
d_fpc_246 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_74 (coe v0)
-- Once.CCC.Machine.FlatStoreWF.loc-below
d_loc'45'below_248 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_loc'45'below_248 = erased
-- Once.CCC.Machine.FlatStoreWF.sv-below
d_sv'45'below_256 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_sv'45'below_256 = erased
-- Once.CCC.Machine.FlatStoreWF.svm-below
d_svm'45'below_268 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_svm'45'below_268 = erased
-- Once.CCC.Machine.FlatStoreWF.mloc-below
d_mloc'45'below_276 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  ()
d_mloc'45'below_276 = erased
-- Once.CCC.Machine.FlatStoreWF.loc-mono
d_loc'45'mono_290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_loc'45'mono_290 ~v0 ~v1 ~v2 v3 v4 v5
  = du_loc'45'mono_290 v3 v4 v5
du_loc'45'mono_290 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_loc'45'mono_290 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v2)
             (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.sv-mono
d_sv'45'mono_304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_sv'45'mono_304 ~v0 ~v1 ~v2 v3 v4 v5 = du_sv'45'mono_304 v3 v4 v5
du_sv'45'mono_304 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_sv'45'mono_304 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v3
        -> coe du_loc'45'mono_290 (coe v3) (coe v1) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.svm-mono
d_svm'45'mono_318 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_svm'45'mono_318 ~v0 ~v1 ~v2 v3 v4 v5
  = du_svm'45'mono_318 v3 v4 v5
du_svm'45'mono_318 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_svm'45'mono_318 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe du_sv'45'mono_304 (coe v3) (coe v1) (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.sv-as-loc-below
d_sv'45'as'45'loc'45'below_330 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny
d_sv'45'as'45'loc'45'below_330 ~v0 ~v1 v2 v3
  = du_sv'45'as'45'loc'45'below_330 v2 v3
du_sv'45'as'45'loc'45'below_330 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny
du_sv'45'as'45'loc'45'below_330 v0 v1
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
d_slot'45'base'45'below_356 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny
d_slot'45'base'45'below_356 ~v0 ~v1 v2 v3
  = du_slot'45'base'45'below_356 v2 v3
du_slot'45'base'45'below_356 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny
du_slot'45'base'45'below_356 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe du_sv'45'as'45'loc'45'below_330 (coe v2) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.sucLoc-below
d_sucLoc'45'below_370 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> AgdaAny
d_sucLoc'45'below_370 ~v0 ~v1 v2 v3 = du_sucLoc'45'below_370 v2 v3
du_sucLoc'45'below_370 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> AgdaAny
du_sucLoc'45'below_370 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe seq (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.offsetLoc-below
d_offsetLoc'45'below_392 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> AgdaAny -> AgdaAny
d_offsetLoc'45'below_392 ~v0 ~v1 v2 ~v3 v4
  = du_offsetLoc'45'below_392 v2 v4
du_offsetLoc'45'below_392 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> AgdaAny
du_offsetLoc'45'below_392 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe seq (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.sv-succ-below
d_sv'45'succ'45'below_416 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
d_sv'45'succ'45'below_416 ~v0 ~v1 v2
  = du_sv'45'succ'45'below_416 v2
du_sv'45'succ'45'below_416 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
du_sv'45'succ'45'below_416 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatStoreWF.sv-pred-below
d_sv'45'pred'45'below_430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
d_sv'45'pred'45'below_430 ~v0 ~v1 v2
  = du_sv'45'pred'45'below_430 v2
du_sv'45'pred'45'below_430 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
du_sv'45'pred'45'below_430 v0
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
d_StoreWF_446 a0 a1 a2 = ()
data T_StoreWF_446
  = C_constructor_488 (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
                       AgdaAny)
                      (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny)
                      (AgdaAny -> Integer -> AgdaAny)
-- Once.CCC.Machine.FlatStoreWF.StoreWF.wf-regs
d_wf'45'regs_472 ::
  T_StoreWF_446 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
d_wf'45'regs_472 v0
  = case coe v0 of
      C_constructor_488 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.StoreWF.wf-heap
d_wf'45'heap_476 ::
  T_StoreWF_446 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny
d_wf'45'heap_476 v0
  = case coe v0 of
      C_constructor_488 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.StoreWF.wf-stack
d_wf'45'stack_482 :: T_StoreWF_446 -> AgdaAny -> Integer -> AgdaAny
d_wf'45'stack_482 v0
  = case coe v0 of
      C_constructor_488 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.StoreWF.wf-fresh
d_wf'45'fresh_486 ::
  T_StoreWF_446 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wf'45'fresh_486 = erased
-- Once.CCC.Machine.FlatStoreWF.rw-below
d_rw'45'below_500 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_rw'45'below_500 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du_rw'45'below_500 v3 v4 v6 v7
du_rw'45'below_500 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_rw'45'below_500 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56 -> coe v2
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62 -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58 -> coe v2
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62 -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60 -> coe v2
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62 -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60 -> coe v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62 -> coe v2
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-write-reg
d_wf'45'write'45'reg_638 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_446 -> AgdaAny -> T_StoreWF_446
d_wf'45'write'45'reg_638 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_wf'45'write'45'reg_638 v3 v5 v6
du_wf'45'write'45'reg_638 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  T_StoreWF_446 -> AgdaAny -> T_StoreWF_446
du_wf'45'write'45'reg_638 v0 v1 v2
  = coe
      C_constructor_488
      (\ v3 ->
         coe
           du_rw'45'below_500 (coe v0) (coe v3) (coe v2)
           (coe d_wf'45'regs_472 v1 v3))
      (d_wf'45'heap_476 (coe v1)) (d_wf'45'stack_482 (coe v1))
-- Once.CCC.Machine.FlatStoreWF.wf-halt
d_wf'45'halt_658 :: T_StoreWF_446 -> T_StoreWF_446
d_wf'45'halt_658 v0 = coe v0
-- Once.CCC.Machine.FlatStoreWF.wf-write-reg-halt
d_wf'45'write'45'reg'45'halt_672 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Bool -> T_StoreWF_446 -> AgdaAny -> T_StoreWF_446
d_wf'45'write'45'reg'45'halt_672 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du_wf'45'write'45'reg'45'halt_672 v3 v6 v7
du_wf'45'write'45'reg'45'halt_672 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  T_StoreWF_446 -> AgdaAny -> T_StoreWF_446
du_wf'45'write'45'reg'45'halt_672 v0 v1 v2
  = coe
      C_constructor_488
      (\ v3 ->
         coe
           du_rw'45'below_500 (coe v0) (coe v3) (coe v2)
           (coe d_wf'45'regs_472 v1 v3))
      (d_wf'45'heap_476 (coe v1)) (d_wf'45'stack_482 (coe v1))
-- Once.CCC.Machine.FlatStoreWF.regs-ss
d_regs'45'ss_698 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> AgdaAny
d_regs'45'ss_698 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_regs'45'ss_698 v4 v5
du_regs'45'ss_698 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> AgdaAny
du_regs'45'ss_698 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatStoreWF.wf-stack-slot
d_wf'45'stack'45'slot_738 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  Integer -> T_StoreWF_446 -> T_StoreWF_446
d_wf'45'stack'45'slot_738 ~v0 ~v1 ~v2 ~v3 v4
  = du_wf'45'stack'45'slot_738 v4
du_wf'45'stack'45'slot_738 :: T_StoreWF_446 -> T_StoreWF_446
du_wf'45'stack'45'slot_738 v0
  = coe
      C_constructor_488
      (\ v1 ->
         coe du_regs'45'ss_698 (coe v1) (coe d_wf'45'regs_472 v0 v1))
      (d_wf'45'heap_476 (coe v0)) (d_wf'45'stack_482 (coe v0))
-- Once.CCC.Machine.FlatStoreWF.wsm-below
d_wsm'45'below_768 ::
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
d_wsm'45'below_768 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 v10 v11
  = du_wsm'45'below_768 v6 v7 v10 v11
du_wsm'45'below_768 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_wsm'45'below_768 v0 v1 v2 v3
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
d_wf'45'write'45'stack_804 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_446 -> AgdaAny -> T_StoreWF_446
d_wf'45'write'45'stack_804 v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du_wf'45'write'45'stack_804 v0 v3 v4 v6 v7
du_wf'45'write'45'stack_804 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> T_StoreWF_446 -> AgdaAny -> T_StoreWF_446
du_wf'45'write'45'stack_804 v0 v1 v2 v3 v4
  = coe
      C_constructor_488 (d_wf'45'regs_472 (coe v3))
      (d_wf'45'heap_476 (coe v3))
      (\ v5 v6 ->
         coe
           du_wsm'45'below_768
           (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__84 v0 v1 v5)
           (coe
              MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v2) (coe v6))
           (coe d_wf'45'stack_482 v3 v5 v6) (coe v4))
-- Once.CCC.Machine.FlatStoreWF.whm-below
d_whm'45'below_836 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_whm'45'below_836 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8
  = du_whm'45'below_836 v4 v7 v8
du_whm'45'below_836 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_whm'45'below_836 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe seq (coe v4) (coe v2)
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.whm-fresh
d_whm'45'fresh_866 ::
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
d_whm'45'fresh_866 = erased
-- Once.CCC.Machine.FlatStoreWF.wf-write-heap
d_wf'45'write'45'heap_896 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_446 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> T_StoreWF_446
d_wf'45'write'45'heap_896 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7
  = du_wf'45'write'45'heap_896 v3 v5 v7
du_wf'45'write'45'heap_896 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoreWF_446 -> AgdaAny -> T_StoreWF_446
du_wf'45'write'45'heap_896 v0 v1 v2
  = coe
      C_constructor_488 (d_wf'45'regs_472 (coe v1))
      (\ v3 ->
         coe
           du_whm'45'below_836
           (coe
              MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__80 (coe v0)
              (coe v3))
           (coe d_wf'45'heap_476 v1 v3) (coe v2))
      (d_wf'45'stack_482 (coe v1))
-- Once.CCC.Machine.FlatStoreWF.wf-write-loc
d_wf'45'write'45'loc_926 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_446 -> AgdaAny -> AgdaAny -> T_StoreWF_446
d_wf'45'write'45'loc_926 v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_wf'45'write'45'loc_926 v0 v3 v4 v5 v7
du_wf'45'write'45'loc_926 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_446 -> AgdaAny -> T_StoreWF_446
du_wf'45'write'45'loc_926 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v5 v6
        -> coe
             du_wf'45'write'45'stack_804 (coe v0) (coe v5) (coe v6) (coe v3)
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v5
        -> case coe v2 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v6
               -> case coe v6 of
                    MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v7 v8
                      -> coe v3
                    MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v7
                      -> coe du_wf'45'write'45'heap_896 (coe v5) (coe v3) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v6
               -> coe du_wf'45'write'45'heap_896 (coe v5) (coe v3) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v6 v7 v8
               -> coe du_wf'45'write'45'heap_896 (coe v5) (coe v3) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v6
               -> coe du_wf'45'write'45'heap_896 (coe v5) (coe v3) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.readLoc-below
d_readLoc'45'below_990 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_446 -> AgdaAny
d_readLoc'45'below_990 ~v0 ~v1 ~v2 v3 v4
  = du_readLoc'45'below_990 v3 v4
du_readLoc'45'below_990 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_446 -> AgdaAny
du_readLoc'45'below_990 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe d_wf'45'stack_482 v1 v2 v3
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe d_wf'45'heap_476 v1 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-load-value
d_wf'45'load'45'value_1010 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_446 -> AgdaAny -> T_StoreWF_446
d_wf'45'load'45'value_1010 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_wf'45'load'45'value_1010 v3 v4 v5 v6
du_wf'45'load'45'value_1010 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_446 -> AgdaAny -> T_StoreWF_446
du_wf'45'load'45'value_1010 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe du_wf'45'write'45'reg_638 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-load-resolved
d_wf'45'load'45'resolved_1032 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_446 -> AgdaAny -> T_StoreWF_446
d_wf'45'load'45'resolved_1032 ~v0 ~v1 v2 v3 v4 v5 ~v6
  = du_wf'45'load'45'resolved_1032 v2 v3 v4 v5
du_wf'45'load'45'resolved_1032 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_446 -> T_StoreWF_446
du_wf'45'load'45'resolved_1032 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_wf'45'load'45'value_1010 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_646 (coe v0)
                (coe v4))
             (coe v3) (coe du_readLoc'45'below_990 (coe v4) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-load-suc-resolved
d_wf'45'load'45'suc'45'resolved_1052 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_446 -> AgdaAny -> T_StoreWF_446
d_wf'45'load'45'suc'45'resolved_1052 ~v0 ~v1 v2 v3 v4 v5 ~v6
  = du_wf'45'load'45'suc'45'resolved_1052 v2 v3 v4 v5
du_wf'45'load'45'suc'45'resolved_1052 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_446 -> T_StoreWF_446
du_wf'45'load'45'suc'45'resolved_1052 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_wf'45'load'45'value_1010 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_646 (coe v0)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v4)))
             (coe v3)
             (coe
                du_readLoc'45'below_990
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v4))
                (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-store-resolved
d_wf'45'store'45'resolved_1078 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_446 -> AgdaAny -> AgdaAny -> T_StoreWF_446
d_wf'45'store'45'resolved_1078 v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_wf'45'store'45'resolved_1078 v0 v3 v4 v5 v7
du_wf'45'store'45'resolved_1078 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_446 -> AgdaAny -> T_StoreWF_446
du_wf'45'store'45'resolved_1078 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_wf'45'write'45'loc_926 (coe v0) (coe v5) (coe v2) (coe v3)
             (coe v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-store-suc-resolved
d_wf'45'store'45'suc'45'resolved_1102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_446 -> AgdaAny -> AgdaAny -> T_StoreWF_446
d_wf'45'store'45'suc'45'resolved_1102 v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_wf'45'store'45'suc'45'resolved_1102 v0 v3 v4 v5 v7
du_wf'45'store'45'suc'45'resolved_1102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_446 -> AgdaAny -> T_StoreWF_446
du_wf'45'store'45'suc'45'resolved_1102 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_wf'45'write'45'loc_926 (coe v0)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v5))
             (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-lea-indexed
d_wf'45'lea'45'indexed_1130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_StoreWF_446 -> AgdaAny -> T_StoreWF_446
d_wf'45'lea'45'indexed_1130 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_wf'45'lea'45'indexed_1130 v3 v5 v6
du_wf'45'lea'45'indexed_1130 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_446 -> AgdaAny -> T_StoreWF_446
du_wf'45'lea'45'indexed_1130 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_wf'45'write'45'reg_638
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v1)
             (coe du_offsetLoc'45'below_392 (coe v3) (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-slot-load
d_wf'45'slot'45'load_1156 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_446 -> AgdaAny -> T_StoreWF_446
d_wf'45'slot'45'load_1156 ~v0 ~v1 ~v2 = du_wf'45'slot'45'load_1156
du_wf'45'slot'45'load_1156 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_446 -> AgdaAny -> T_StoreWF_446
du_wf'45'slot'45'load_1156 = coe du_wf'45'load'45'value_1010
-- Once.CCC.Machine.FlatStoreWF.structured-pure-sigop-below
d_structured'45'pure'45'sigop'45'below_1168
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.FlatStoreWF.structured-pure-sigop-below"
-- Once.CCC.Machine.FlatStoreWF.pure-out-val-below
d_pure'45'out'45'val'45'below_1182 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 -> Maybe AgdaAny -> AgdaAny
d_pure'45'out'45'val'45'below_1182 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_pure'45'out'45'val'45'below_1182 v6
du_pure'45'out'45'val'45'below_1182 :: Maybe AgdaAny -> AgdaAny
du_pure'45'out'45'val'45'below_1182 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatStoreWF.sigop-output-below
d_sigop'45'output'45'below_1208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 -> AgdaAny
d_sigop'45'output'45'below_1208 v0 v1 v2 v3 v4 v5
  = coe
      d_go_1238 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_212 (coe v4))
-- Once.CCC.Machine.FlatStoreWF._.aux
d_aux_1228 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
d_aux_1228 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> coe
                    du_pure'45'out'45'val'45'below_1182
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2444 (coe v2)
                       (coe v9) (coe v5))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    du_pure'45'out'45'val'45'below_1182
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg'45'typed_2438
                       (coe v2)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_152
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468 (coe v5))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             d_structured'45'pure'45'sigop'45'below_1168 v0 v1 v2 v3 v4 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF._.go
d_go_1238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 -> AgdaAny
d_go_1238 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_124
        -> coe
             d_aux_1228 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_204 (coe v3))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1234
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_152
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468 (coe v5))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
      MAlonzo.Code.Once.SigOp.Info.C_Emits_126
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.SigOp.Info.C_Halts_128
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-slot-load-out
d_wf'45'slot'45'load'45'out_1246 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  T_StoreWF_446 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'slot'45'load'45'out_1246 ~v0 v1 ~v2 v3 v4 v5
  = du_wf'45'slot'45'load'45'out_1246 v1 v3 v4 v5
du_wf'45'slot'45'load'45'out_1246 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  T_StoreWF_446 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf'45'slot'45'load'45'out_1246 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_638
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v2)
                (coe v3))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v1)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-slot-load-in1
d_wf'45'slot'45'load'45'in1_1270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  T_StoreWF_446 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'slot'45'load'45'in1_1270 ~v0 v1 ~v2 v3 v4 v5
  = du_wf'45'slot'45'load'45'in1_1270 v1 v3 v4 v5
du_wf'45'slot'45'load'45'in1_1270 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  T_StoreWF_446 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf'45'slot'45'load'45'in1_1270 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_638
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v2)
                (coe v3))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v1)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.Preserves
d_Preserves_1292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_Preserves_1292 = erased
-- Once.CCC.Machine.FlatStoreWF.wf-abstract
d_wf'45'abstract_1308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  T_StoreWF_446 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'abstract_1308 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_638
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
                (coe
                   d_wf'45'regs_472 v4
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_638
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v4)
                (coe
                   d_wf'45'regs_472 v4
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2082
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_638
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58) (coe v4)
                (coe
                   d_wf'45'regs_472 v4
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2084
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_638
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
                (coe
                   d_wf'45'regs_472 v4
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2086
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'load'45'resolved_1032 (coe v2)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1234
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_152
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468 (coe v2))
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                (coe v4))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2088
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'load'45'suc'45'resolved_1052 (coe v2)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1234
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_152
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468 (coe v2))
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                (coe v4))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090 v5
        -> coe
             du_wf'45'slot'45'load'45'out_1246
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_646 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_586
                      (coe v3))
                   (coe v5)))
             (coe v3) (coe v4)
             (coe
                du_readLoc'45'below_990
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_586
                      (coe v3))
                   (coe v5))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'loc_926 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_586
                      (coe v3))
                   (coe v5))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_152
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                (coe v4)
                (coe
                   d_wf'45'regs_472 v4
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2094
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'store'45'resolved_1078 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1234
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_152
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468 (coe v2))
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_152
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                (coe v4)
                (coe
                   d_wf'45'regs_472 v4
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2096
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'store'45'suc'45'resolved_1102 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1234
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_152
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468 (coe v2))
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_152
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                (coe v4)
                (coe
                   d_wf'45'regs_472 v4
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2098 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_638
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2100 v5
        -> coe
             du_wf'45'slot'45'load'45'in1_1270
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_646 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_586
                      (coe v3))
                   (coe v5)))
             (coe v3) (coe v4)
             (coe
                du_readLoc'45'below_990
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_586
                      (coe v3))
                   (coe v5))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2102 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_wf'45'stack'45'slot_738 (coe v4))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2104 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_wf'45'stack'45'slot_738 (coe v4))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2106 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2108 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_wf'45'stack'45'slot_738 (coe v4))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2110
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2112
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2114 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2116 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'loc_926 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_586
                      (coe v3))
                   (coe v5))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_152
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                (coe v4)
                (coe
                   d_wf'45'regs_472 v4
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2118 v5
        -> coe
             du_wf'45'slot'45'load'45'out_1246
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_646 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_586
                      (coe v3))
                   (coe v5)))
             (coe v3) (coe v4)
             (coe
                du_readLoc'45'below_990
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_586
                      (coe v3))
                   (coe v5))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2120 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2126 v5 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg'45'halt_672
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
                (coe
                   d_sigop'45'output'45'below_1208 (coe v0)
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                      (coe v3))
                   (coe v5) (coe v6) (coe v7) (coe v2)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2130 v5 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_638
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2132 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_638
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2136 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_638
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v4)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2138 v5 v6
        -> coe
             d_wf'45'case_1328 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_case'45'tag'45'at_2570
                (coe v2))
             (coe v5) (coe v6) (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2140 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_constructor_488
                (\ v6 ->
                   coe
                     du_rw'45'below_500
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v6)
                     (coe
                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                        (coe
                           addInt (coe (1 :: Integer))
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                              (coe v3))))
                     (coe
                        du_sv'45'mono_304
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_152
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468 (coe v2))
                           (coe v6))
                        (coe
                           MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                              (coe v3)))
                        (coe d_wf'45'regs_472 v4 v6)))
                (\ v6 ->
                   coe
                     du_svm'45'mono_318
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_472 v2 v6)
                     (coe
                        MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                           (coe v3)))
                     (coe d_wf'45'heap_476 v4 v6))
                (\ v6 v7 ->
                   coe
                     du_svm'45'mono_318
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_470 v2 v6 v7)
                     (coe
                        MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                           (coe v3)))
                     (coe d_wf'45'stack_482 v4 v6 v7)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2142 v5
        -> coe
             d_wf'45'loop_1338 (coe v0) (coe (1000000 :: Integer)) (coe v5)
             (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2144 v5
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_424
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_wf'45'write'45'reg_638
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62) (coe v4)
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                          (coe v3)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_426
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_wf'45'write'45'reg_638
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62) (coe v4)
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                          (coe v3)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_428
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_wf'45'write'45'reg_638
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62) (coe v4)
                       (coe
                          du_sv'45'pred'45'below_430
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_152
                             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468 (coe v2))
                             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62))))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                          (coe v3)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_430
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_wf'45'write'45'reg_638
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62) (coe v4)
                       (coe
                          d_wf'45'regs_472 v4
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58)))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                          (coe v3)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_input2'45'zero_432
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_wf'45'write'45'reg_638
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58) (coe v4)
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                          (coe v3)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_input2'45'inc_434
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_wf'45'write'45'reg_638
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58) (coe v4)
                       (coe
                          du_sv'45'succ'45'below_416
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_152
                             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468 (coe v2))
                             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58))))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                          (coe v3)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2148 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'lea'45'indexed_1130
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_slot'45'base_1354
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_646 (coe v2)
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_586
                            (coe v3))
                         (coe v5))))
                (coe v4)
                (coe
                   du_slot'45'base'45'below_356
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_646 (coe v2)
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_586
                            (coe v3))
                         (coe v5)))
                   (coe
                      du_readLoc'45'below_990
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_586
                            (coe v3))
                         (coe v5))
                      (coe v4))))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-trace
d_wf'45'trace_1316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  T_StoreWF_446 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'trace_1316 v0 v1 v2 v3 v4
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v3)))
      (:) v5 v6
        -> let v7
                 = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_474 (coe v2) in
           coe
             (if coe v7
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                             (coe v3)))
                else coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_wf'45'trace_1316 (coe v0) (coe v6)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2584
                                   (coe v0) (coe v5) (coe v2) (coe v3)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2584
                                   (coe v0) (coe v5) (coe v2) (coe v3)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   d_wf'45'abstract_1308 (coe v0) (coe v5) (coe v2) (coe v3)
                                   (coe v4)))))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_wf'45'abstract_1308 (coe v0) (coe v5) (coe v2) (coe v3)
                                (coe v4)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_wf'45'trace_1316 (coe v0) (coe v6)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2584
                                      (coe v0) (coe v5) (coe v2) (coe v3)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2584
                                      (coe v0) (coe v5) (coe v2) (coe v3)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_wf'45'abstract_1308 (coe v0) (coe v5) (coe v2) (coe v3)
                                      (coe v4)))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-case
d_wf'45'case_1328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  T_StoreWF_446 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'case_1328 v0 v1 v2 v3 v4 v5 v6
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v7 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                          (coe v5)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v8
               -> case coe v8 of
                    0 -> coe
                           d_wf'45'trace_1316 (coe v0) (coe v2) (coe v4) (coe v5) (coe v6)
                    _ -> coe
                           d_wf'45'trace_1316 (coe v0) (coe v3) (coe v4) (coe v5) (coe v6)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v8 v9 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                          (coe v5)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                          (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-loop
d_wf'45'loop_1338 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  T_StoreWF_446 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'loop_1338 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                   (coe v4)))
      _ -> let v6 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v7
                    = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_474 (coe v3) in
              coe
                (if coe v7
                   then coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                                (coe v4)))
                   else (let v8
                               = MAlonzo.Code.Once.CCC.Machine.SMCore.d_scratch_146
                                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468 (coe v3)) in
                         coe
                           (case coe v8 of
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v9
                                -> coe
                                     d_wf'45'loop'45'go_1348 (coe v0) (coe v6) (coe v2) (coe v3)
                                     (coe v4) (coe v5)
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v9
                                -> case coe v9 of
                                     0 -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                            (coe
                                               MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                                                  (coe v4)))
                                     _ -> coe
                                            d_wf'45'loop'45'go_1348 (coe v0) (coe v6) (coe v2)
                                            (coe v3) (coe v4) (coe v5)
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v9 v10 v11
                                -> coe
                                     d_wf'45'loop'45'go_1348 (coe v0) (coe v6) (coe v2) (coe v3)
                                     (coe v4) (coe v5)
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v9
                                -> coe
                                     d_wf'45'loop'45'go_1348 (coe v0) (coe v6) (coe v2) (coe v3)
                                     (coe v4) (coe v5)
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Machine.FlatStoreWF.wf-loop-go
d_wf'45'loop'45'go_1348 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  T_StoreWF_446 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'loop'45'go_1348 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_rec_1868 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe du_step_1852 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_rec_1868 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))))
-- Once.CCC.Machine.FlatStoreWF._.step
d_step_1852 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  T_StoreWF_446 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_1852 v0 ~v1 v2 v3 v4 v5 = du_step_1852 v0 v2 v3 v4 v5
du_step_1852 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  T_StoreWF_446 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_1852 v0 v1 v2 v3 v4
  = coe
      d_wf'45'trace_1316 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.CCC.Machine.FlatStoreWF._.ls'
d_ls''_1854 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  T_StoreWF_446 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_ls''_1854 v0 ~v1 v2 v3 v4 ~v5 = du_ls''_1854 v0 v2 v3 v4
du_ls''_1854 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
du_ls''_1854 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2586 (coe v0)
         (coe v1) (coe v2) (coe v3))
-- Once.CCC.Machine.FlatStoreWF._.al'
d_al''_1856 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  T_StoreWF_446 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510
d_al''_1856 v0 ~v1 v2 v3 v4 ~v5 = du_al''_1856 v0 v2 v3 v4
du_al''_1856 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510
du_al''_1856 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2586 (coe v0)
         (coe v1) (coe v2) (coe v3))
-- Once.CCC.Machine.FlatStoreWF._.ls''
d_ls''''_1858 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  T_StoreWF_446 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_ls''''_1858 v0 ~v1 v2 v3 v4 ~v5 = du_ls''''_1858 v0 v2 v3 v4
du_ls''''_1858 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
du_ls''''_1858 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_476
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468
         (coe du_ls''_1854 (coe v0) (coe v1) (coe v2) (coe v3)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_470 (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_472
         (coe du_ls''_1854 (coe v0) (coe v1) (coe v2) (coe v3)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_474
         (coe du_ls''_1854 (coe v0) (coe v1) (coe v2) (coe v3)))
-- Once.CCC.Machine.FlatStoreWF._.al''
d_al''''_1860 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  T_StoreWF_446 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510
d_al''''_1860 v0 ~v1 v2 v3 v4 ~v5 = du_al''''_1860 v0 v2 v3 v4
du_al''''_1860 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510
du_al''''_1860 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_594
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_586
         (coe v3))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_588
         (coe du_al''_1856 (coe v0) (coe v1) (coe v2) (coe v3)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_590 (coe v3))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
         (coe du_al''_1856 (coe v0) (coe v1) (coe v2) (coe v3)))
-- Once.CCC.Machine.FlatStoreWF._.wf''
d_wf''''_1862 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  T_StoreWF_446 -> T_StoreWF_446
d_wf''''_1862 v0 ~v1 v2 v3 v4 v5 = du_wf''''_1862 v0 v2 v3 v4 v5
du_wf''''_1862 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  T_StoreWF_446 -> T_StoreWF_446
du_wf''''_1862 v0 v1 v2 v3 v4
  = coe
      C_constructor_488
      (d_wf'45'regs_472
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe du_step_1852 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))))
      (d_wf'45'heap_476
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe du_step_1852 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))))
      (\ v5 v6 ->
         coe
           du_svm'45'mono_318
           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_470 v2 v5 v6)
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
              (coe du_step_1852 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)))
           (coe d_wf'45'stack_482 v4 v5 v6))
-- Once.CCC.Machine.FlatStoreWF._.rec
d_rec_1868 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  T_StoreWF_446 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rec_1868 v0 v1 v2 v3 v4 v5
  = coe
      d_wf'45'loop_1338 (coe v0) (coe v1) (coe v2)
      (coe du_ls''''_1858 (coe v0) (coe v2) (coe v3) (coe v4))
      (coe du_al''''_1860 (coe v0) (coe v2) (coe v3) (coe v4))
      (coe du_wf''''_1862 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Machine.FlatStoreWF.FlatWF
d_FlatWF_1870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_FlatWF_1870 = erased
-- Once.CCC.Machine.FlatStoreWF.wf-jump
d_wf'45'jump_1878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_StoreWF_446 -> T_StoreWF_446
d_wf'45'jump_1878 ~v0 v1 ~v2 v3 = du_wf'45'jump_1878 v1 v3
du_wf'45'jump_1878 ::
  Maybe Integer -> T_StoreWF_446 -> T_StoreWF_446
du_wf'45'jump_1878 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatStoreWF.wf-branch
d_wf'45'branch_1898 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_StoreWF_446 -> T_StoreWF_446
d_wf'45'branch_1898 v0 v1 v2 v3 ~v4 v5
  = du_wf'45'branch_1898 v0 v1 v2 v3 v5
du_wf'45'branch_1898 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  T_StoreWF_446 -> T_StoreWF_446
du_wf'45'branch_1898 v0 v1 v2 v3 v4
  = if coe v1
      then coe
             du_wf'45'jump_1878
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_142 (coe v0)
                (coe v3) (coe v2))
             (coe v4)
      else coe v4
-- Once.CCC.Machine.FlatStoreWF.flat-wf-step
d_flat'45'wf'45'step_1922 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_StoreWF_446 -> T_StoreWF_446
d_flat'45'wf'45'step_1922 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2082
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2084
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2086
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2088
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2094
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2096
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2098 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2100 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2102 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2104 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2106 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2108 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2110
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2112
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2114 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2116 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2118 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2120 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2126 v5 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2130 v5 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2132 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2136 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2138 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2140 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2142 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2144 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146 v5
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2068 v6 -> coe v4
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2070 v6
               -> coe
                    du_wf'45'jump_1878
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_142 (coe v0)
                       (coe v2) (coe v6))
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2072 v6
               -> coe
                    du_wf'45'branch_1898 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_78
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_152
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468
                             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3)))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)))
                    (coe v6) (coe v2) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2074 v6
               -> coe
                    du_wf'45'branch_1898 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_80
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_92
                          (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))))
                    (coe v6) (coe v2) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2148 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
