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
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2864
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'case'45'dispatch_2870
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'from'45'slot'45'with'45'value_2550
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'loop'45'run_2798
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'restore'45'input'45'with'45'value_2562
-- Once.CCC.Machine.FlatStoreWF._.exec-sigop-output
d_exec'45'sigop'45'output_118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output_118 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output_2748
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output'45'of_120 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output'45'of_2738
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2866 (coe v0)
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'alloc_2792
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'loc_2786
-- Once.CCC.Machine.FlatStoreWF._.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_192 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'aux_154 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'aux_2702
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_156 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_192 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'val_156 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_pure'45'sigop'45'out'45'val_2686
      (coe v0) v2 v3 v4 v5
-- Once.CCC.Machine.FlatStoreWF._.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_structured'45'pure'45'sigop'45'output_168 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_structured'45'pure'45'sigop'45'output_2674
      v0
-- Once.CCC.Machine.FlatStoreWF._.CallPost
d_CallPost_174 a0 a1 a2 = ()
-- Once.CCC.Machine.FlatStoreWF._.FlatState
d_FlatState_176 a0 = ()
-- Once.CCC.Machine.FlatStoreWF._.do-branch
d_do'45'branch_196 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'branch_196 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'branch_766 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.do-call
d_do'45'call_200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call_200 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call_1168 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.do-jump
d_do'45'jump_214 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'jump_214 ~v0 = du_do'45'jump_214
du_do'45'jump_214 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'jump_214
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_750
-- Once.CCC.Machine.FlatStoreWF._.do-ret
d_do'45'ret_216 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'ret_216 ~v0 = du_do'45'ret_216
du_do'45'ret_216 ::
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'ret_216
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'ret_968
-- Once.CCC.Machine.FlatStoreWF._.do-thunk
d_do'45'thunk_230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'thunk_230 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'thunk_1102 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.flat-exec-instr
d_flat'45'exec'45'instr_296 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_296 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1330
      (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.FlatState.falloc
d_falloc_444 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_falloc_444 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.FlatState.fclosure
d_fclosure_446 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_446 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.FlatState.flink
d_flink_448 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_448 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.FlatState.floc
d_floc_450 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_450 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.FlatState.fpc
d_fpc_452 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_452 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Machine.FlatStoreWF._.FlatState.fret
d_fret_454 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_454 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Machine.FlatStoreWF.loc-below
d_loc'45'below_464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_loc'45'below_464 = erased
-- Once.CCC.Machine.FlatStoreWF.sv-below
d_sv'45'below_472 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_sv'45'below_472 = erased
-- Once.CCC.Machine.FlatStoreWF.svm-below
d_svm'45'below_484 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_svm'45'below_484 = erased
-- Once.CCC.Machine.FlatStoreWF.mloc-below
d_mloc'45'below_492 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  ()
d_mloc'45'below_492 = erased
-- Once.CCC.Machine.FlatStoreWF.loc-mono
d_loc'45'mono_506 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_loc'45'mono_506 ~v0 ~v1 ~v2 v3 v4 v5
  = du_loc'45'mono_506 v3 v4 v5
du_loc'45'mono_506 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_loc'45'mono_506 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v2)
             (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.sv-mono
d_sv'45'mono_520 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_sv'45'mono_520 ~v0 ~v1 ~v2 v3 v4 v5 = du_sv'45'mono_520 v3 v4 v5
du_sv'45'mono_520 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_sv'45'mono_520 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v3
        -> coe du_loc'45'mono_506 (coe v3) (coe v1) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.svm-mono
d_svm'45'mono_534 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_svm'45'mono_534 ~v0 ~v1 ~v2 v3 v4 v5
  = du_svm'45'mono_534 v3 v4 v5
du_svm'45'mono_534 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_svm'45'mono_534 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe du_sv'45'mono_520 (coe v3) (coe v1) (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.sv-as-loc-below
d_sv'45'as'45'loc'45'below_546 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny
d_sv'45'as'45'loc'45'below_546 ~v0 ~v1 v2 v3
  = du_sv'45'as'45'loc'45'below_546 v2 v3
du_sv'45'as'45'loc'45'below_546 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny
du_sv'45'as'45'loc'45'below_546 v0 v1
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
d_slot'45'base'45'below_572 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny
d_slot'45'base'45'below_572 ~v0 ~v1 v2 v3
  = du_slot'45'base'45'below_572 v2 v3
du_slot'45'base'45'below_572 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny
du_slot'45'base'45'below_572 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe du_sv'45'as'45'loc'45'below_546 (coe v2) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.sucLoc-below
d_sucLoc'45'below_586 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> AgdaAny
d_sucLoc'45'below_586 ~v0 ~v1 v2 v3 = du_sucLoc'45'below_586 v2 v3
du_sucLoc'45'below_586 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> AgdaAny
du_sucLoc'45'below_586 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe seq (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.offsetLoc-below
d_offsetLoc'45'below_608 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> AgdaAny -> AgdaAny
d_offsetLoc'45'below_608 ~v0 ~v1 v2 ~v3 v4
  = du_offsetLoc'45'below_608 v2 v4
du_offsetLoc'45'below_608 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> AgdaAny
du_offsetLoc'45'below_608 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe seq (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.sv-succ-below
d_sv'45'succ'45'below_632 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
d_sv'45'succ'45'below_632 ~v0 ~v1 v2
  = du_sv'45'succ'45'below_632 v2
du_sv'45'succ'45'below_632 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
du_sv'45'succ'45'below_632 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatStoreWF.sv-pred-below
d_sv'45'pred'45'below_646 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
d_sv'45'pred'45'below_646 ~v0 ~v1 v2
  = du_sv'45'pred'45'below_646 v2
du_sv'45'pred'45'below_646 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
du_sv'45'pred'45'below_646 v0
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
d_StoreWF_662 a0 a1 a2 = ()
data T_StoreWF_662
  = C_constructor_704 (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
                       AgdaAny)
                      (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny)
                      (AgdaAny -> Integer -> AgdaAny)
-- Once.CCC.Machine.FlatStoreWF.StoreWF.wf-regs
d_wf'45'regs_688 ::
  T_StoreWF_662 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
d_wf'45'regs_688 v0
  = case coe v0 of
      C_constructor_704 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.StoreWF.wf-heap
d_wf'45'heap_692 ::
  T_StoreWF_662 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny
d_wf'45'heap_692 v0
  = case coe v0 of
      C_constructor_704 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.StoreWF.wf-stack
d_wf'45'stack_698 :: T_StoreWF_662 -> AgdaAny -> Integer -> AgdaAny
d_wf'45'stack_698 v0
  = case coe v0 of
      C_constructor_704 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.StoreWF.wf-fresh
d_wf'45'fresh_702 ::
  T_StoreWF_662 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wf'45'fresh_702 = erased
-- Once.CCC.Machine.FlatStoreWF.rw-below
d_rw'45'below_716 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_rw'45'below_716 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du_rw'45'below_716 v3 v4 v6 v7
du_rw'45'below_716 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_rw'45'below_716 v0 v1 v2 v3
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
d_wf'45'write'45'reg_854 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_662 -> AgdaAny -> T_StoreWF_662
d_wf'45'write'45'reg_854 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_wf'45'write'45'reg_854 v3 v5 v6
du_wf'45'write'45'reg_854 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  T_StoreWF_662 -> AgdaAny -> T_StoreWF_662
du_wf'45'write'45'reg_854 v0 v1 v2
  = coe
      C_constructor_704
      (\ v3 ->
         coe
           du_rw'45'below_716 (coe v0) (coe v3) (coe v2)
           (coe d_wf'45'regs_688 v1 v3))
      (d_wf'45'heap_692 (coe v1)) (d_wf'45'stack_698 (coe v1))
-- Once.CCC.Machine.FlatStoreWF.wf-halt
d_wf'45'halt_874 :: T_StoreWF_662 -> T_StoreWF_662
d_wf'45'halt_874 v0 = coe v0
-- Once.CCC.Machine.FlatStoreWF.wf-write-reg-halt
d_wf'45'write'45'reg'45'halt_888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Bool -> T_StoreWF_662 -> AgdaAny -> T_StoreWF_662
d_wf'45'write'45'reg'45'halt_888 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du_wf'45'write'45'reg'45'halt_888 v3 v6 v7
du_wf'45'write'45'reg'45'halt_888 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  T_StoreWF_662 -> AgdaAny -> T_StoreWF_662
du_wf'45'write'45'reg'45'halt_888 v0 v1 v2
  = coe
      C_constructor_704
      (\ v3 ->
         coe
           du_rw'45'below_716 (coe v0) (coe v3) (coe v2)
           (coe d_wf'45'regs_688 v1 v3))
      (d_wf'45'heap_692 (coe v1)) (d_wf'45'stack_698 (coe v1))
-- Once.CCC.Machine.FlatStoreWF.wsm-below
d_wsm'45'below_924 ::
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
d_wsm'45'below_924 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 v10 v11
  = du_wsm'45'below_924 v6 v7 v10 v11
du_wsm'45'below_924 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_wsm'45'below_924 v0 v1 v2 v3
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
d_wf'45'write'45'stack_960 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_662 -> AgdaAny -> T_StoreWF_662
d_wf'45'write'45'stack_960 v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du_wf'45'write'45'stack_960 v0 v3 v4 v6 v7
du_wf'45'write'45'stack_960 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> T_StoreWF_662 -> AgdaAny -> T_StoreWF_662
du_wf'45'write'45'stack_960 v0 v1 v2 v3 v4
  = coe
      C_constructor_704 (d_wf'45'regs_688 (coe v3))
      (d_wf'45'heap_692 (coe v3))
      (\ v5 v6 ->
         coe
           du_wsm'45'below_924
           (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__88 v0 v1 v5)
           (coe
              MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v2) (coe v6))
           (coe d_wf'45'stack_698 v3 v5 v6) (coe v4))
-- Once.CCC.Machine.FlatStoreWF.whm-below
d_whm'45'below_992 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_whm'45'below_992 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8
  = du_whm'45'below_992 v4 v7 v8
du_whm'45'below_992 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_whm'45'below_992 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe seq (coe v4) (coe v2)
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.whm-fresh
d_whm'45'fresh_1022 ::
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
d_whm'45'fresh_1022 = erased
-- Once.CCC.Machine.FlatStoreWF.wf-write-heap
d_wf'45'write'45'heap_1052 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_662 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> T_StoreWF_662
d_wf'45'write'45'heap_1052 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7
  = du_wf'45'write'45'heap_1052 v3 v5 v7
du_wf'45'write'45'heap_1052 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoreWF_662 -> AgdaAny -> T_StoreWF_662
du_wf'45'write'45'heap_1052 v0 v1 v2
  = coe
      C_constructor_704 (d_wf'45'regs_688 (coe v1))
      (\ v3 ->
         coe
           du_whm'45'below_992
           (coe
              MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__80 (coe v0)
              (coe v3))
           (coe d_wf'45'heap_692 v1 v3) (coe v2))
      (d_wf'45'stack_698 (coe v1))
-- Once.CCC.Machine.FlatStoreWF.wf-write-loc
d_wf'45'write'45'loc_1082 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_662 -> AgdaAny -> AgdaAny -> T_StoreWF_662
d_wf'45'write'45'loc_1082 v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_wf'45'write'45'loc_1082 v0 v3 v4 v5 v7
du_wf'45'write'45'loc_1082 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_662 -> AgdaAny -> T_StoreWF_662
du_wf'45'write'45'loc_1082 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v5 v6
        -> coe
             du_wf'45'write'45'stack_960 (coe v0) (coe v5) (coe v6) (coe v3)
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v5
        -> case coe v2 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v6
               -> coe
                    seq (coe v6)
                    (coe du_wf'45'write'45'heap_1052 (coe v5) (coe v3) (coe v4))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v6
               -> coe du_wf'45'write'45'heap_1052 (coe v5) (coe v3) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v6 v7 v8
               -> coe du_wf'45'write'45'heap_1052 (coe v5) (coe v3) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v6
               -> coe du_wf'45'write'45'heap_1052 (coe v5) (coe v3) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.readLoc-below
d_readLoc'45'below_1154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_662 -> AgdaAny
d_readLoc'45'below_1154 ~v0 ~v1 ~v2 v3 v4
  = du_readLoc'45'below_1154 v3 v4
du_readLoc'45'below_1154 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_662 -> AgdaAny
du_readLoc'45'below_1154 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe d_wf'45'stack_698 v1 v2 v3
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe d_wf'45'heap_692 v1 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-load-value
d_wf'45'load'45'value_1174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_662 -> AgdaAny -> T_StoreWF_662
d_wf'45'load'45'value_1174 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_wf'45'load'45'value_1174 v3 v4 v5 v6
du_wf'45'load'45'value_1174 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_662 -> AgdaAny -> T_StoreWF_662
du_wf'45'load'45'value_1174 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe du_wf'45'write'45'reg_854 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-load-resolved
d_wf'45'load'45'resolved_1196 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_662 -> AgdaAny -> T_StoreWF_662
d_wf'45'load'45'resolved_1196 ~v0 ~v1 v2 v3 v4 v5 ~v6
  = du_wf'45'load'45'resolved_1196 v2 v3 v4 v5
du_wf'45'load'45'resolved_1196 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_662 -> T_StoreWF_662
du_wf'45'load'45'resolved_1196 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_wf'45'load'45'value_1174 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644 (coe v0)
                (coe v4))
             (coe v3) (coe du_readLoc'45'below_1154 (coe v4) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-load-suc-resolved
d_wf'45'load'45'suc'45'resolved_1216 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_662 -> AgdaAny -> T_StoreWF_662
d_wf'45'load'45'suc'45'resolved_1216 ~v0 ~v1 v2 v3 v4 v5 ~v6
  = du_wf'45'load'45'suc'45'resolved_1216 v2 v3 v4 v5
du_wf'45'load'45'suc'45'resolved_1216 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_662 -> T_StoreWF_662
du_wf'45'load'45'suc'45'resolved_1216 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_wf'45'load'45'value_1174 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644 (coe v0)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v4)))
             (coe v3)
             (coe
                du_readLoc'45'below_1154
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v4))
                (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-store-resolved
d_wf'45'store'45'resolved_1242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_662 -> AgdaAny -> AgdaAny -> T_StoreWF_662
d_wf'45'store'45'resolved_1242 v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_wf'45'store'45'resolved_1242 v0 v3 v4 v5 v7
du_wf'45'store'45'resolved_1242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_662 -> AgdaAny -> T_StoreWF_662
du_wf'45'store'45'resolved_1242 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_wf'45'write'45'loc_1082 (coe v0) (coe v5) (coe v2) (coe v3)
             (coe v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-store-suc-resolved
d_wf'45'store'45'suc'45'resolved_1266 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_662 -> AgdaAny -> AgdaAny -> T_StoreWF_662
d_wf'45'store'45'suc'45'resolved_1266 v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_wf'45'store'45'suc'45'resolved_1266 v0 v3 v4 v5 v7
du_wf'45'store'45'suc'45'resolved_1266 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_662 -> AgdaAny -> T_StoreWF_662
du_wf'45'store'45'suc'45'resolved_1266 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_wf'45'write'45'loc_1082 (coe v0)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v5))
             (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-lea-indexed
d_wf'45'lea'45'indexed_1294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_StoreWF_662 -> AgdaAny -> T_StoreWF_662
d_wf'45'lea'45'indexed_1294 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_wf'45'lea'45'indexed_1294 v3 v5 v6
du_wf'45'lea'45'indexed_1294 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoreWF_662 -> AgdaAny -> T_StoreWF_662
du_wf'45'lea'45'indexed_1294 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_wf'45'write'45'reg_854
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v1)
             (coe du_offsetLoc'45'below_608 (coe v3) (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-slot-load
d_wf'45'slot'45'load_1320 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_662 -> AgdaAny -> T_StoreWF_662
d_wf'45'slot'45'load_1320 ~v0 ~v1 ~v2 = du_wf'45'slot'45'load_1320
du_wf'45'slot'45'load_1320 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_StoreWF_662 -> AgdaAny -> T_StoreWF_662
du_wf'45'slot'45'load_1320 = coe du_wf'45'load'45'value_1174
-- Once.CCC.Machine.FlatStoreWF.structured-pure-sigop-below
d_structured'45'pure'45'sigop'45'below_1332
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.FlatStoreWF.structured-pure-sigop-below"
-- Once.CCC.Machine.FlatStoreWF.pure-out-val-below
d_pure'45'out'45'val'45'below_1346 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_192 -> Maybe AgdaAny -> AgdaAny
d_pure'45'out'45'val'45'below_1346 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_pure'45'out'45'val'45'below_1346 v6
du_pure'45'out'45'val'45'below_1346 :: Maybe AgdaAny -> AgdaAny
du_pure'45'out'45'val'45'below_1346 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatStoreWF.sigop-output-below
d_sigop'45'output'45'below_1372 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> AgdaAny
d_sigop'45'output'45'below_1372 v0 v1 v2 v3 v4 v5
  = coe
      d_go_1402 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_216 (coe v4))
-- Once.CCC.Machine.FlatStoreWF._.aux
d_aux_1392 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_192 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
d_aux_1392 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> coe
                    du_pure'45'out'45'val'45'below_1346
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2644 (coe v2)
                       (coe v9) (coe v5))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    du_pure'45'out'45'val'45'below_1346
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg'45'typed_2638
                       (coe v2)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v5))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             d_structured'45'pure'45'sigop'45'below_1332 v0 v1 v2 v3 v4 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF._.go
d_go_1402 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 -> AgdaAny
d_go_1402 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_124
        -> coe
             d_aux_1392 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_200 (coe v3))
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
d_wf'45'slot'45'load'45'out_1410 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_StoreWF_662 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'slot'45'load'45'out_1410 ~v0 v1 ~v2 v3 v4 v5
  = du_wf'45'slot'45'load'45'out_1410 v1 v3 v4 v5
du_wf'45'slot'45'load'45'out_1410 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_StoreWF_662 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf'45'slot'45'load'45'out_1410 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_854
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
d_wf'45'slot'45'load'45'in1_1434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_StoreWF_662 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'slot'45'load'45'in1_1434 ~v0 v1 ~v2 v3 v4 v5
  = du_wf'45'slot'45'load'45'in1_1434 v1 v3 v4 v5
du_wf'45'slot'45'load'45'in1_1434 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_StoreWF_662 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf'45'slot'45'load'45'in1_1434 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_854
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
d_Preserves_1456 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_Preserves_1456 = erased
-- Once.CCC.Machine.FlatStoreWF.BodyPreserves
d_BodyPreserves_1466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  ()
d_BodyPreserves_1466 = erased
-- Once.CCC.Machine.FlatStoreWF.wf-loop-run
d_wf'45'loop'45'run_1482 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   T_StoreWF_662 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_662 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'loop'45'run_1482 v0 v1 v2 v3 v4 v5 v6
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
                                     d_wf'45'loop'45'run'45'go_1492 (coe v0) (coe v1) (coe v7)
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
                                            d_wf'45'loop'45'run'45'go_1492 (coe v0) (coe v1)
                                            (coe v7) (coe v3) (coe v4) (coe v5) (coe v6)
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v10 v11 v12
                                -> coe
                                     d_wf'45'loop'45'run'45'go_1492 (coe v0) (coe v1) (coe v7)
                                     (coe v3) (coe v4) (coe v5) (coe v6)
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v10
                                -> coe
                                     d_wf'45'loop'45'run'45'go_1492 (coe v0) (coe v1) (coe v7)
                                     (coe v3) (coe v4) (coe v5) (coe v6)
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Machine.FlatStoreWF.wf-loop-run-go
d_wf'45'loop'45'run'45'go_1492 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   T_StoreWF_662 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_662 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'loop'45'run'45'go_1492 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_rec_1638 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v6)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe du_step_1626 (coe v3) (coe v4) (coe v5) (coe v6)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_rec_1638 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6))))
-- Once.CCC.Machine.FlatStoreWF._.step
d_step_1626 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   T_StoreWF_662 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_662 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_1626 ~v0 ~v1 ~v2 v3 v4 v5 v6 = du_step_1626 v3 v4 v5 v6
du_step_1626 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   T_StoreWF_662 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_662 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_1626 v0 v1 v2 v3 = coe v2 v0 v1 v3
-- Once.CCC.Machine.FlatStoreWF._.ls''
d_ls''''_1628 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   T_StoreWF_662 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_662 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_ls''''_1628 ~v0 v1 ~v2 v3 v4 ~v5 ~v6 = du_ls''''_1628 v1 v3 v4
du_ls''''_1628 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_ls''''_1628 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'loc_2786
      (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0 v1 v2))
-- Once.CCC.Machine.FlatStoreWF._.al''
d_al''''_1630 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   T_StoreWF_662 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_662 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_al''''_1630 ~v0 v1 ~v2 v3 v4 ~v5 ~v6 = du_al''''_1630 v1 v3 v4
du_al''''_1630 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_al''''_1630 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'alloc_2792
      (coe v2)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0 v1 v2))
-- Once.CCC.Machine.FlatStoreWF._.wf''
d_wf''''_1632 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   T_StoreWF_662 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_662 -> T_StoreWF_662
d_wf''''_1632 ~v0 ~v1 ~v2 v3 v4 v5 v6 = du_wf''''_1632 v3 v4 v5 v6
du_wf''''_1632 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   T_StoreWF_662 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_662 -> T_StoreWF_662
du_wf''''_1632 v0 v1 v2 v3
  = coe
      C_constructor_704
      (d_wf'45'regs_688
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe du_step_1626 (coe v0) (coe v1) (coe v2) (coe v3))))
      (d_wf'45'heap_692
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe du_step_1626 (coe v0) (coe v1) (coe v2) (coe v3))))
      (\ v4 v5 ->
         coe
           du_svm'45'mono_534
           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_416 v0 v4 v5)
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
              (coe du_step_1626 (coe v0) (coe v1) (coe v2) (coe v3)))
           (coe d_wf'45'stack_698 v3 v4 v5))
-- Once.CCC.Machine.FlatStoreWF._.rec
d_rec_1638 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   T_StoreWF_662 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_StoreWF_662 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rec_1638 v0 v1 v2 v3 v4 v5 v6
  = coe
      d_wf'45'loop'45'run_1482 (coe v0) (coe v1) (coe v2)
      (coe du_ls''''_1628 (coe v1) (coe v3) (coe v4))
      (coe du_al''''_1630 (coe v1) (coe v3) (coe v4)) (coe v5)
      (coe du_wf''''_1632 (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.CCC.Machine.FlatStoreWF.wf-abstract
d_wf'45'abstract_1646 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_StoreWF_662 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'abstract_1646 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_wf'45'write'45'reg_854
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v4)
                (coe
                   d_wf'45'regs_688 v4
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
                du_wf'45'write'45'reg_854
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v4)
                (coe
                   d_wf'45'regs_688 v4
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
                du_wf'45'load'45'resolved_1196 (coe v2)
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
                du_wf'45'load'45'suc'45'resolved_1216 (coe v2)
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
             du_wf'45'slot'45'load'45'out_1410
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
                du_readLoc'45'below_1154
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
                du_wf'45'write'45'loc_1082 (coe v0)
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
                   d_wf'45'regs_688 v4
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
                du_wf'45'store'45'resolved_1242 (coe v0)
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
                   d_wf'45'regs_688 v4
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
                du_wf'45'store'45'suc'45'resolved_1266 (coe v0)
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
                   d_wf'45'regs_688 v4
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
                du_wf'45'write'45'reg_854
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v4)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2238 v5
        -> coe
             du_wf'45'slot'45'load'45'in1_1434
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
                du_readLoc'45'below_1154
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
                du_wf'45'write'45'loc_1082 (coe v0)
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
                   d_wf'45'regs_688 v4
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2256 v5
        -> coe
             du_wf'45'slot'45'load'45'out_1410
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
                du_readLoc'45'below_1154
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
                du_wf'45'write'45'reg'45'halt_888
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v4)
                (coe
                   d_sigop'45'output'45'below_1372 (coe v0)
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
                du_wf'45'write'45'reg_854
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
                du_wf'45'write'45'reg_854
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
                du_wf'45'write'45'reg_854
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v4)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2278 v5 v6
        -> coe
             d_wf'45'case_1666 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_case'45'tag'45'at_2770
                (coe v2))
             (coe v5) (coe v6) (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_constructor_704
                (\ v6 ->
                   coe
                     du_rw'45'below_716
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v6)
                     (coe
                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                        (coe
                           addInt (coe (1 :: Integer))
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                              (coe v3))))
                     (coe
                        du_sv'45'mono_520
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v2))
                           (coe v6))
                        (coe
                           MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                              (coe v3)))
                        (coe d_wf'45'regs_688 v4 v6)))
                (\ v6 ->
                   coe
                     du_svm'45'mono_534
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_418 v2 v6)
                     (coe
                        MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                           (coe v3)))
                     (coe d_wf'45'heap_692 v4 v6))
                (\ v6 v7 ->
                   coe
                     du_svm'45'mono_534
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_416 v2 v6 v7)
                     (coe
                        MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                           (coe v3)))
                     (coe d_wf'45'stack_698 v4 v6 v7)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                   (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2282 v5
        -> coe
             d_wf'45'loop'45'run_1482 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2866 (coe v0)
                (coe v5))
             (coe (1000000 :: Integer)) (coe v2) (coe v3)
             (coe d_wf'45'trace_1654 (coe v0) (coe v5)) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284 v5
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_370
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_wf'45'write'45'reg_854
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
                       du_wf'45'write'45'reg_854
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
                       du_wf'45'write'45'reg_854
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60) (coe v4)
                       (coe
                          du_sv'45'pred'45'below_646
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
                       du_wf'45'write'45'reg_854
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60) (coe v4)
                       (coe
                          d_wf'45'regs_688 v4
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
                       du_wf'45'write'45'reg_854
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
                       du_wf'45'write'45'reg_854
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62) (coe v4)
                       (coe
                          du_sv'45'succ'45'below_632
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
                du_wf'45'lea'45'indexed_1294
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
                   du_slot'45'base'45'below_572
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644 (coe v2)
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                            (coe v3))
                         (coe v5)))
                   (coe
                      du_readLoc'45'below_1154
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
d_wf'45'trace_1654 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_StoreWF_662 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'trace_1654 v0 v1 v2 v3 v4
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
                             d_wf'45'trace_1654 (coe v0) (coe v6)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2864
                                   (coe v0) (coe v5) (coe v2) (coe v3)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2864
                                   (coe v0) (coe v5) (coe v2) (coe v3)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   d_wf'45'abstract_1646 (coe v0) (coe v5) (coe v2) (coe v3)
                                   (coe v4)))))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_wf'45'abstract_1646 (coe v0) (coe v5) (coe v2) (coe v3)
                                (coe v4)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_wf'45'trace_1654 (coe v0) (coe v6)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2864
                                      (coe v0) (coe v5) (coe v2) (coe v3)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2864
                                      (coe v0) (coe v5) (coe v2) (coe v3)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_wf'45'abstract_1646 (coe v0) (coe v5) (coe v2) (coe v3)
                                      (coe v4)))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.wf-case
d_wf'45'case_1666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_StoreWF_662 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf'45'case_1666 v0 v1 v2 v3 v4 v5 v6
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
                           d_wf'45'trace_1654 (coe v0) (coe v2) (coe v4) (coe v5) (coe v6)
                    _ -> coe
                           d_wf'45'trace_1654 (coe v0) (coe v3) (coe v4) (coe v5) (coe v6)
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
d_FlatWF_2050 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_FlatWF_2050 = erased
-- Once.CCC.Machine.FlatStoreWF.wf-jump
d_wf'45'jump_2058 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_StoreWF_662 -> T_StoreWF_662
d_wf'45'jump_2058 ~v0 v1 ~v2 v3 = du_wf'45'jump_2058 v1 v3
du_wf'45'jump_2058 ::
  Maybe Integer -> T_StoreWF_662 -> T_StoreWF_662
du_wf'45'jump_2058 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatStoreWF.wf-branch
d_wf'45'branch_2078 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_StoreWF_662 -> T_StoreWF_662
d_wf'45'branch_2078 v0 v1 v2 v3 ~v4 v5
  = du_wf'45'branch_2078 v0 v1 v2 v3 v5
du_wf'45'branch_2078 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_StoreWF_662 -> T_StoreWF_662
du_wf'45'branch_2078 v0 v1 v2 v3 v4
  = if coe v1
      then coe
             du_wf'45'jump_2058
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
                (coe v3) (coe v2))
             (coe v4)
      else coe v4
-- Once.CCC.Machine.FlatStoreWF.wf-ret
d_wf'45'ret_2100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_StoreWF_662 -> T_StoreWF_662
d_wf'45'ret_2100 ~v0 v1 ~v2 v3 = du_wf'45'ret_2100 v1 v3
du_wf'45'ret_2100 :: [Integer] -> T_StoreWF_662 -> T_StoreWF_662
du_wf'45'ret_2100 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatStoreWF.wf-thunk
d_wf'45'thunk_2122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_StoreWF_662 -> T_StoreWF_662
d_wf'45'thunk_2122 v0 v1 v2 v3
  = coe
      C_constructor_704 (d_wf'45'regs_688 (coe v3))
      (d_wf'45'heap_692 (coe v3))
      (d_cleared_2138 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Machine.FlatStoreWF._.cleared
d_cleared_2138 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_StoreWF_662 -> AgdaAny -> Integer -> AgdaAny
d_cleared_2138 v0 v1 v2 v3 v4 v5
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
                                    else coe seq (coe v11) (coe d_wf'45'stack_698 v3 v4 v5)
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   else coe seq (coe v9) (coe d_wf'45'stack_698 v3 v4 v5)
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.CCC.Machine.FlatStoreWF.wf-call
d_wf'45'call_2164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_StoreWF_662 -> T_StoreWF_662
d_wf'45'call_2164 v0 v1 v2 v3
  = coe
      du_go_2176 (coe v3)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_callView_1196 (coe v0)
         (coe v1) (coe v2))
-- Once.CCC.Machine.FlatStoreWF._.go
d_go_2176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_StoreWF_662 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1178 -> T_StoreWF_662
d_go_2176 ~v0 ~v1 ~v2 v3 v4 = du_go_2176 v3 v4
du_go_2176 ::
  T_StoreWF_662 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1178 -> T_StoreWF_662
du_go_2176 v0 v1 = coe seq (coe v1) (coe v0)
-- Once.CCC.Machine.FlatStoreWF.cl-jump
d_cl'45'jump_2200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> AgdaAny
d_cl'45'jump_2200 ~v0 v1 ~v2 v3 = du_cl'45'jump_2200 v1 v3
du_cl'45'jump_2200 :: Maybe Integer -> AgdaAny -> AgdaAny
du_cl'45'jump_2200 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatStoreWF.cl-branch
d_cl'45'branch_2220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> AgdaAny
d_cl'45'branch_2220 v0 v1 v2 v3 ~v4 v5
  = du_cl'45'branch_2220 v0 v1 v2 v3 v5
du_cl'45'branch_2220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  AgdaAny -> AgdaAny
du_cl'45'branch_2220 v0 v1 v2 v3 v4
  = if coe v1
      then coe
             du_cl'45'jump_2200
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
                (coe v3) (coe v2))
             (coe v4)
      else coe v4
-- Once.CCC.Machine.FlatStoreWF.cl-ret
d_cl'45'ret_2242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> AgdaAny
d_cl'45'ret_2242 ~v0 v1 ~v2 v3 = du_cl'45'ret_2242 v1 v3
du_cl'45'ret_2242 :: [Integer] -> AgdaAny -> AgdaAny
du_cl'45'ret_2242 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatStoreWF.cl-call
d_cl'45'call_2264 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> AgdaAny
d_cl'45'call_2264 v0 v1 v2 v3
  = coe
      du_go_2276 (coe v3)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_callView_1196 (coe v0)
         (coe v1) (coe v2))
-- Once.CCC.Machine.FlatStoreWF._.go
d_go_2276 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1178 -> AgdaAny
d_go_2276 ~v0 ~v1 ~v2 v3 v4 = du_go_2276 v3 v4
du_go_2276 ::
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1178 -> AgdaAny
du_go_2276 v0 v1 = coe seq (coe v1) (coe v0)
-- Once.CCC.Machine.FlatStoreWF.cl-step
d_cl'45'step_2302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_StoreWF_662 -> AgdaAny -> AgdaAny
d_cl'45'step_2302 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228 v6
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230 v6
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2236 v6
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2238 v6
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2240 v6
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2242 v6
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2244 v6
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2246 v6
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2248
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2250
        -> coe d_cl'45'call_2264 (coe v0) (coe v2) (coe v3) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2252 v6
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2254 v6
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2256 v6
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2258 v6
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2264 v6 v7 v8
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2270 v6 v7 v8
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2272 v6
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2274
        -> coe
             d_wf'45'regs_688 v4
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276 v6
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2278 v6 v7
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280 v6
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2282 v6
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284 v6
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286 v6
        -> case coe v6 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206 v7 -> coe v5
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208 v7
               -> coe
                    du_cl'45'jump_2200
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
                       (coe v2) (coe v7))
                    (coe v5)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2210 v7
               -> coe
                    du_cl'45'branch_2220 (coe v0)
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
                    du_cl'45'branch_2220 (coe v0)
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
                    du_cl'45'ret_2242
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v3))
                    (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2288 v6
        -> coe
             du_sv'45'mono_520
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_wf'45'abstract_1646 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                   (coe v4)))
             (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStoreWF.flat-wf-step
d_flat'45'wf'45'step_2662 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_StoreWF_662 -> T_StoreWF_662
d_flat'45'wf'45'step_2662 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2236 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2238 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2240 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2242 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2244 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2246 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2248
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2250
        -> coe d_wf'45'call_2164 (coe v0) (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2252 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2254 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2256 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2258 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2264 v5 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2270 v5 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2272 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2274
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2278 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2282 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286 v5
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206 v6 -> coe v4
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208 v6
               -> coe
                    du_wf'45'jump_2058
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
                       (coe v2) (coe v6))
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2210 v6
               -> coe
                    du_wf'45'branch_2078 (coe v0)
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
                    du_wf'45'branch_2078 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_106
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_118
                          (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))))
                    (coe v6) (coe v2) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2214 v6 v7
               -> coe d_wf'45'thunk_2122 (coe v0) (coe v7) (coe v3) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2216 v6
               -> coe
                    du_wf'45'ret_2100
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v3))
                    (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2288 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
             (coe
                d_wf'45'abstract_1646 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
