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

module MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.FlatStackPtr
import qualified MAlonzo.Code.Once.CCC.Machine.FlatStoreWF
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Machine.FlatPtrBounds._.readLoc
d_readLoc_26 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_readLoc_26 ~v0 = du_readLoc_26
du_readLoc_26 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_readLoc_26
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712
-- Once.CCC.Machine.FlatPtrBounds._.writeHeapMem-aux
d_writeHeapMem'45'aux_32 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_writeHeapMem'45'aux_32 ~v0 = du_writeHeapMem'45'aux_32
du_writeHeapMem'45'aux_32 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_writeHeapMem'45'aux_32 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem'45'aux_844 v2
      v3 v4
-- Once.CCC.Machine.FlatPtrBounds._.writeLoc
d_writeLoc_34 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_writeLoc_34 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_878 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.writeLocToHeap
d_writeLocToHeap_50 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_writeLocToHeap_50 ~v0 = du_writeLocToHeap_50
du_writeLocToHeap_50 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_writeLocToHeap_50
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_870
-- Once.CCC.Machine.FlatPtrBounds._.writeLocToStack
d_writeLocToStack_52 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_writeLocToStack_52 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLocToStack_860 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.writeStackMem-aux
d_writeStackMem'45'aux_56 ::
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
d_writeStackMem'45'aux_56 ~v0 = du_writeStackMem'45'aux_56
du_writeStackMem'45'aux_56 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_writeStackMem'45'aux_56 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeStackMem'45'aux_732 v4
      v5 v6 v7
-- Once.CCC.Machine.FlatPtrBounds._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_68 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'load'45'suc'45'via'45'resolved_68 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_68
du_exec'45'load'45'suc'45'via'45'resolved_68 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_exec'45'load'45'suc'45'via'45'resolved_68
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'suc'45'via'45'resolved_1570
-- Once.CCC.Machine.FlatPtrBounds._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_70 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'load'45'via'45'resolved_70 ~v0
  = du_exec'45'load'45'via'45'resolved_70
du_exec'45'load'45'via'45'resolved_70 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_exec'45'load'45'via'45'resolved_70
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'via'45'resolved_1532
-- Once.CCC.Machine.FlatPtrBounds._.exec-load-with-value
d_exec'45'load'45'with'45'value_72 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'load'45'with'45'value_72 ~v0
  = du_exec'45'load'45'with'45'value_72
du_exec'45'load'45'with'45'value_72 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_exec'45'load'45'with'45'value_72
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'with'45'value_1520
-- Once.CCC.Machine.FlatPtrBounds._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_74 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'store'45'suc'45'via'45'resolved_74 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'suc'45'via'45'resolved_1582
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_76 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'store'45'via'45'resolved_76 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'via'45'resolved_1544
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.exec-abstract
d_exec'45'abstract_92 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_92 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2870
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_102 ~v0
  = du_exec'45'load'45'from'45'slot'45'with'45'value_102
du_exec'45'load'45'from'45'slot'45'with'45'value_102 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_102
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'from'45'slot'45'with'45'value_2566
-- Once.CCC.Machine.FlatPtrBounds._.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_112 ~v0
  = du_exec'45'restore'45'input'45'with'45'value_112
du_exec'45'restore'45'input'45'with'45'value_112 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_112
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'restore'45'input'45'with'45'value_2578
-- Once.CCC.Machine.FlatPtrBounds._.exec-sigop-output
d_exec'45'sigop'45'output_118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_exec'45'sigop'45'output_118 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output_2764
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_exec'45'sigop'45'output'45'of_120 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output'45'of_2754
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_152 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_pure'45'sigop'45'out'45'aux_152 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'aux_2718
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_pure'45'sigop'45'out'45'val_154 ~v0
  = du_pure'45'sigop'45'out'45'val_154
du_pure'45'sigop'45'out'45'val_154 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_pure'45'sigop'45'out'45'val_154 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_pure'45'sigop'45'out'45'val_2702
      v1 v2 v3 v4
-- Once.CCC.Machine.FlatPtrBounds._.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_166 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_structured'45'pure'45'sigop'45'output_166 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_structured'45'pure'45'sigop'45'output_2690
      v0
-- Once.CCC.Machine.FlatPtrBounds._.CallPost
d_CallPost_172 a0 a1 a2 = ()
-- Once.CCC.Machine.FlatPtrBounds._.FlatState
d_FlatState_174 a0 = ()
-- Once.CCC.Machine.FlatPtrBounds._.do-branch
d_do'45'branch_188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'branch_188 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'branch_512 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.do-call
d_do'45'call_190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call_190 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call_914 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.do-jump
d_do'45'jump_198 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'jump_198 ~v0 = du_do'45'jump_198
du_do'45'jump_198 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'jump_198
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_504
-- Once.CCC.Machine.FlatPtrBounds._.do-ret
d_do'45'ret_200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'ret_200 ~v0 = du_do'45'ret_200
du_do'45'ret_200 ::
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'ret_200
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'ret_714
-- Once.CCC.Machine.FlatPtrBounds._.do-thunk
d_do'45'thunk_214 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'thunk_214 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'thunk_848 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.flat-exec-instr
d_flat'45'exec'45'instr_268 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_268 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1076
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.falloc
d_falloc_350 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_falloc_350 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.fclosure
d_fclosure_352 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fclosure_352 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_88 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.floc
d_floc_354 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_floc_354 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.fpc
d_fpc_356 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_356 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_84 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.fret
d_fret_358 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_358 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_86 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF
d_StoreWF_368 a0 a1 a2 = ()
-- Once.CCC.Machine.FlatPtrBounds._.sv-below
d_sv'45'below_372 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_sv'45'below_372 = erased
-- Once.CCC.Machine.FlatPtrBounds._.svm-below
d_svm'45'below_374 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_svm'45'below_374 = erased
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF.wf-fresh
d_wf'45'fresh_384 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_558 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wf'45'fresh_384 = erased
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF.wf-heap
d_wf'45'heap_386 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_558 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny
d_wf'45'heap_386 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'heap_588 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF.wf-regs
d_wf'45'regs_388 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_558 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
d_wf'45'regs_388 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'regs_584 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF.wf-stack
d_wf'45'stack_390 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_558 ->
  AgdaAny -> Integer -> AgdaAny
d_wf'45'stack_390 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'stack_594
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds.PtrB
d_PtrB_392 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_PtrB_392 = erased
-- Once.CCC.Machine.FlatPtrBounds.PtrB?
d_PtrB'63'_400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_PtrB'63'_400 = erased
-- Once.CCC.Machine.FlatPtrBounds.PBInv
d_PBInv_412 a0 a1 a2 = ()
data T_PBInv_412
  = C_mkPtrBounds_446 (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
                       AgdaAny)
                      (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny)
                      (AgdaAny -> Integer -> AgdaAny)
-- Once.CCC.Machine.FlatPtrBounds.PBInv.pb-regs
d_pb'45'regs_434 ::
  T_PBInv_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
d_pb'45'regs_434 v0
  = case coe v0 of
      C_mkPtrBounds_446 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.PBInv.pb-heap
d_pb'45'heap_438 ::
  T_PBInv_412 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny
d_pb'45'heap_438 v0
  = case coe v0 of
      C_mkPtrBounds_446 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.PBInv.pb-stack
d_pb'45'stack_444 :: T_PBInv_412 -> AgdaAny -> Integer -> AgdaAny
d_pb'45'stack_444 v0
  = case coe v0 of
      C_mkPtrBounds_446 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.PtrBoundsWF
d_PtrBoundsWF_448 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_PtrBoundsWF_448 = erased
-- Once.CCC.Machine.FlatPtrBounds.ptr-bounds-suc
d_ptr'45'bounds'45'suc_458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_PBInv_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ptr'45'bounds'45'suc_458 ~v0 ~v1 v2 ~v3 v4 ~v5
  = du_ptr'45'bounds'45'suc_458 v2 v4
du_ptr'45'bounds'45'suc_458 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  T_PBInv_412 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ptr'45'bounds'45'suc_458 v0 v1 = coe d_pb'45'regs_434 v1 v0
-- Once.CCC.Machine.FlatPtrBounds.ptr-bounds-cell
d_ptr'45'bounds'45'cell_476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_PBInv_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ptr'45'bounds'45'cell_476 ~v0 ~v1 v2 v3 v4 ~v5
  = du_ptr'45'bounds'45'cell_476 v2 v3 v4
du_ptr'45'bounds'45'cell_476 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_PBInv_412 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ptr'45'bounds'45'cell_476 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50
               (coe v1))))
      (coe du_ptr'45'bounds'45'suc_458 (coe v0) (coe v2))
-- Once.CCC.Machine.FlatPtrBounds.size-with-new
d_size'45'with'45'new_494 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_size'45'with'45'new_494 = erased
-- Once.CCC.Machine.FlatPtrBounds.size-with-old
d_size'45'with'45'old_528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_size'45'with'45'old_528 = erased
-- Once.CCC.Machine.FlatPtrBounds.ptrb-ext
d_ptrb'45'ext_574 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_ptrb'45'ext_574 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_ptrb'45'ext_574 v4 v6
du_ptrb'45'ext_574 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny
du_ptrb'45'ext_574 v0 v1
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
-- Once.CCC.Machine.FlatPtrBounds.pbm-ext
d_pbm'45'ext_622 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_pbm'45'ext_622 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_pbm'45'ext_622 v4 v6
du_pbm'45'ext_622 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny
du_pbm'45'ext_622 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe du_ptrb'45'ext_574 (coe v2) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-halt
d_pb'45'halt_648 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Bool -> T_PBInv_412 -> T_PBInv_412
d_pb'45'halt_648 ~v0 ~v1 ~v2 ~v3 v4 = du_pb'45'halt_648 v4
du_pb'45'halt_648 :: T_PBInv_412 -> T_PBInv_412
du_pb'45'halt_648 v0 = coe v0
-- Once.CCC.Machine.FlatPtrBounds.pb-write-reg
d_pb'45'write'45'reg_666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_412 -> T_PBInv_412
d_pb'45'write'45'reg_666 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'write'45'reg_666 v3 v5 v6
du_pb'45'write'45'reg_666 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> T_PBInv_412 -> T_PBInv_412
du_pb'45'write'45'reg_666 v0 v1 v2
  = coe
      C_mkPtrBounds_446
      (coe
         (\ v3 ->
            coe
              du_go_686 (coe v1) (coe v2) (coe v3)
              (coe
                 MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.du_readReg'45'write_484
                 (coe v0) (coe v3))))
      (coe d_pb'45'heap_438 (coe v2)) (coe d_pb'45'stack_444 (coe v2))
-- Once.CCC.Machine.FlatPtrBounds._.go
d_go_686 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny ->
  T_PBInv_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_go_686 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 = du_go_686 v5 v6 v7 v8
du_go_686 ::
  AgdaAny ->
  T_PBInv_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_go_686 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> coe d_pb'45'regs_434 v1 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-write-reg-halt
d_pb'45'write'45'reg'45'halt_716 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Bool -> AgdaAny -> T_PBInv_412 -> T_PBInv_412
d_pb'45'write'45'reg'45'halt_716 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du_pb'45'write'45'reg'45'halt_716 v3 v6 v7
du_pb'45'write'45'reg'45'halt_716 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> T_PBInv_412 -> T_PBInv_412
du_pb'45'write'45'reg'45'halt_716 v0 v1 v2
  = coe du_pb'45'write'45'reg_666 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.FlatPtrBounds.pb-wsm-aux
d_pb'45'wsm'45'aux_750 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_pb'45'wsm'45'aux_750 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 v10
                       v11
  = du_pb'45'wsm'45'aux_750 v6 v7 v10 v11
du_pb'45'wsm'45'aux_750 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_pb'45'wsm'45'aux_750 v0 v1 v2 v3
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
-- Once.CCC.Machine.FlatPtrBounds.pb-whm-aux
d_pb'45'whm'45'aux_788 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_pb'45'whm'45'aux_788 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8
  = du_pb'45'whm'45'aux_788 v4 v7 v8
du_pb'45'whm'45'aux_788 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_pb'45'whm'45'aux_788 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe seq (coe v4) (coe v2)
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-write-stack
d_pb'45'write'45'stack_816 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_412 -> T_PBInv_412
d_pb'45'write'45'stack_816 v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du_pb'45'write'45'stack_816 v0 v3 v4 v6 v7
du_pb'45'write'45'stack_816 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> AgdaAny -> T_PBInv_412 -> T_PBInv_412
du_pb'45'write'45'stack_816 v0 v1 v2 v3 v4
  = coe
      C_mkPtrBounds_446 (coe d_pb'45'regs_434 (coe v4))
      (coe d_pb'45'heap_438 (coe v4))
      (coe
         (\ v5 v6 ->
            coe
              du_pb'45'wsm'45'aux_750
              (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__84 v0 v1 v5)
              (coe
                 MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v2) (coe v6))
              (coe d_pb'45'stack_444 v4 v5 v6) (coe v3)))
-- Once.CCC.Machine.FlatPtrBounds.pb-write-heap
d_pb'45'write'45'heap_844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_412 -> T_PBInv_412
d_pb'45'write'45'heap_844 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'write'45'heap_844 v3 v5 v6
du_pb'45'write'45'heap_844 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> T_PBInv_412 -> T_PBInv_412
du_pb'45'write'45'heap_844 v0 v1 v2
  = coe
      C_mkPtrBounds_446 (coe d_pb'45'regs_434 (coe v2))
      (coe
         (\ v3 ->
            coe
              du_pb'45'whm'45'aux_788
              (coe
                 MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__80 (coe v0)
                 (coe v3))
              (coe d_pb'45'heap_438 v2 v3) (coe v1)))
      (coe d_pb'45'stack_444 (coe v2))
-- Once.CCC.Machine.FlatPtrBounds.pb-write-mem
d_pb'45'write'45'mem_868 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_412 -> T_PBInv_412
d_pb'45'write'45'mem_868 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'write'45'mem_868 v0 v3 v5 v6
du_pb'45'write'45'mem_868 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_PBInv_412 -> T_PBInv_412
du_pb'45'write'45'mem_868 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             du_pb'45'write'45'stack_816 (coe v0) (coe v4) (coe v5) (coe v2)
             (coe v3)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> coe du_pb'45'write'45'heap_844 (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-read-loc
d_pb'45'read'45'loc_902 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_PBInv_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
d_pb'45'read'45'loc_902 ~v0 ~v1 ~v2 v3 v4
  = du_pb'45'read'45'loc_902 v3 v4
du_pb'45'read'45'loc_902 ::
  T_PBInv_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
du_pb'45'read'45'loc_902 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe d_pb'45'stack_444 v0 v2 v3
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe d_pb'45'heap_438 v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-load-value
d_pb'45'load'45'value_930 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_412 -> T_PBInv_412
d_pb'45'load'45'value_930 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_pb'45'load'45'value_930 v3 v4 v5 v6
du_pb'45'load'45'value_930 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_412 -> T_PBInv_412
du_pb'45'load'45'value_930 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe du_pb'45'write'45'reg_666 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-load-resolved
d_pb'45'load'45'resolved_962 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_PBInv_412 -> T_PBInv_412
d_pb'45'load'45'resolved_962 ~v0 ~v1 v2 v3 v4 v5
  = du_pb'45'load'45'resolved_962 v2 v3 v4 v5
du_pb'45'load'45'resolved_962 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_PBInv_412 -> T_PBInv_412
du_pb'45'load'45'resolved_962 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_pb'45'load'45'value_930 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v0)
                (coe v4))
             (coe du_pb'45'read'45'loc_902 (coe v3) (coe v4)) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-load-suc-resolved
d_pb'45'load'45'suc'45'resolved_990 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_PBInv_412 -> T_PBInv_412
d_pb'45'load'45'suc'45'resolved_990 ~v0 ~v1 v2 v3 v4 v5
  = du_pb'45'load'45'suc'45'resolved_990 v2 v3 v4 v5
du_pb'45'load'45'suc'45'resolved_990 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_PBInv_412 -> T_PBInv_412
du_pb'45'load'45'suc'45'resolved_990 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_pb'45'load'45'value_930 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v0)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v4)))
             (coe
                du_pb'45'read'45'loc_902 (coe v3)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v4)))
             (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-store-resolved
d_pb'45'store'45'resolved_1018 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_412 -> T_PBInv_412
d_pb'45'store'45'resolved_1018 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'store'45'resolved_1018 v0 v3 v5 v6
du_pb'45'store'45'resolved_1018 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_PBInv_412 -> T_PBInv_412
du_pb'45'store'45'resolved_1018 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_pb'45'write'45'mem_868 (coe v0) (coe v4) (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-store-suc-resolved
d_pb'45'store'45'suc'45'resolved_1050 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_412 -> T_PBInv_412
d_pb'45'store'45'suc'45'resolved_1050 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'store'45'suc'45'resolved_1050 v0 v3 v5 v6
du_pb'45'store'45'suc'45'resolved_1050 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_PBInv_412 -> T_PBInv_412
du_pb'45'store'45'suc'45'resolved_1050 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_pb'45'write'45'mem_868 (coe v0)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v4))
             (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-from-slot
d_pb'45'from'45'slot_1080 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_412 -> T_PBInv_412
d_pb'45'from'45'slot_1080 ~v0 ~v1 ~v2 v3 v4 v5
  = du_pb'45'from'45'slot_1080 v3 v4 v5
du_pb'45'from'45'slot_1080 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_412 -> T_PBInv_412
du_pb'45'from'45'slot_1080 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_pb'45'write'45'reg_666
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v1)
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-restore
d_pb'45'restore_1106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_412 -> T_PBInv_412
d_pb'45'restore_1106 ~v0 ~v1 ~v2 v3 v4 v5
  = du_pb'45'restore_1106 v3 v4 v5
du_pb'45'restore_1106 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_412 -> T_PBInv_412
du_pb'45'restore_1106 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_pb'45'write'45'reg_666
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v1)
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-pred
d_pb'45'pred_1130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
d_pb'45'pred_1130 ~v0 ~v1 v2 = du_pb'45'pred_1130 v2
du_pb'45'pred_1130 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
du_pb'45'pred_1130 v0
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
-- Once.CCC.Machine.FlatPtrBounds.pb-succ
d_pb'45'succ_1156 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
d_pb'45'succ_1156 ~v0 ~v1 v2 = du_pb'45'succ_1156 v2
du_pb'45'succ_1156 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
du_pb'45'succ_1156 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatPtrBounds.pb-reg-op
d_pb'45'reg'45'op_1182 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_448 ->
  T_PBInv_412 -> T_PBInv_412
d_pb'45'reg'45'op_1182 ~v0 ~v1 v2 v3 v4
  = du_pb'45'reg'45'op_1182 v2 v3 v4
du_pb'45'reg'45'op_1182 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_448 ->
  T_PBInv_412 -> T_PBInv_412
du_pb'45'reg'45'op_1182 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_450
        -> coe
             du_pb'45'write'45'reg_666
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_452
        -> coe
             du_pb'45'write'45'reg_666
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_454
        -> coe
             du_pb'45'write'45'reg_666
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe
                du_pb'45'pred_1130
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v0))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)))
             (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_456
        -> coe
             du_pb'45'write'45'reg_666
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe
                d_pb'45'regs_434 v2
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64))
             (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_458
        -> coe
             du_pb'45'write'45'reg_666
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_460
        -> coe
             du_pb'45'write'45'reg_666
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64)
             (coe
                du_pb'45'succ_1156
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v0))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64)))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.structured-pure-sigop-inbounds
d_structured'45'pure'45'sigop'45'inbounds_1230
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.FlatPtrBounds.structured-pure-sigop-inbounds"
-- Once.CCC.Machine.FlatPtrBounds.sigop-output-pb
d_sigop'45'output'45'pb_1242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 -> AgdaAny
d_sigop'45'output'45'pb_1242 v0 v1 v2 v3 v4 v5
  = coe
      d_go_1284 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_212 (coe v4))
-- Once.CCC.Machine.FlatPtrBounds._.pov
d_pov_1262 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 -> Maybe AgdaAny -> AgdaAny
d_pov_1262 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_pov_1262 v7
du_pov_1262 :: Maybe AgdaAny -> AgdaAny
du_pov_1262 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatPtrBounds._.aux
d_aux_1274 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
d_aux_1274 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> coe
                    du_pov_1262
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2660 (coe v2)
                       (coe v9) (coe v5))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    du_pov_1262
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg'45'typed_2654
                       (coe v2)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v5))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             d_structured'45'pure'45'sigop'45'inbounds_1230 v0 v1 v2 v3 v4 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds._.go
d_go_1284 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 -> AgdaAny
d_go_1284 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_124
        -> coe
             d_aux_1274 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_204 (coe v3))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1428
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v5))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
      MAlonzo.Code.Once.SigOp.Info.C_Emits_126
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.SigOp.Info.C_Halts_128
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-abstract
d_pb'45'abstract_1294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_558 ->
  T_PBInv_412 -> T_PBInv_412
d_pb'45'abstract_1294 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2288
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'write'45'reg_666
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe
                     d_pb'45'regs_434 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2290
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'write'45'reg_666
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
                  (coe
                     d_pb'45'regs_434 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2292
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'write'45'reg_666
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58)
                  (coe
                     d_pb'45'regs_434 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2294
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'write'45'reg_666
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe
                     d_pb'45'regs_434 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2296
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'load'45'resolved_962 (coe v2)
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1428
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2298
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'load'45'suc'45'resolved_990 (coe v2)
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1428
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2300 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'from'45'slot_1080
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v3)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                           (coe v4))
                        (coe v2)))
                  (coe
                     du_pb'45'read'45'loc_902 (coe v8)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                           (coe v4))
                        (coe v2)))
                  (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2302 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'write'45'mem_868 (coe v0)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                        (coe v4))
                     (coe v2))
                  (coe
                     d_pb'45'regs_434 v8
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2304
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'store'45'resolved_1018 (coe v0)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1428
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                  (coe
                     d_pb'45'regs_434 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2306
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'store'45'suc'45'resolved_1050 (coe v0)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1428
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                  (coe
                     d_pb'45'regs_434 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2308 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'write'45'reg_666
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2310 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'restore_1106
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v3)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                           (coe v4))
                        (coe v2)))
                  (coe
                     du_pb'45'read'45'loc_902 (coe v8)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                           (coe v4))
                        (coe v2)))
                  (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2312 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2314 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2316 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2318 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2320
        -> coe (\ v2 v3 v4 v5 v6 v7 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2322
        -> coe (\ v2 v3 v4 v5 v6 v7 -> v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2324 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2326 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'write'45'mem_868 (coe v0)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                        (coe v4))
                     (coe v2))
                  (coe
                     d_pb'45'regs_434 v8
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2328 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'from'45'slot_1080
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v3)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                           (coe v4))
                        (coe v2)))
                  (coe
                     du_pb'45'read'45'loc_902 (coe v8)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                           (coe v4))
                        (coe v2)))
                  (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2330 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2336 v2 v3 v4
        -> coe
             (\ v5 v6 v7 v8 v9 v10 ->
                coe
                  du_pb'45'write'45'reg'45'halt_716
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe
                     d_sigop'45'output'45'pb_1242 (coe v0)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2870
                              (coe v0) (coe v1) (coe v5) (coe v6))))
                     (coe v2) (coe v3) (coe v4) (coe v5))
                  (coe v10))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2340 v2 v3 v4
        -> coe
             (\ v5 v6 v7 v8 v9 v10 ->
                coe
                  du_pb'45'write'45'reg_666
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v10))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2342 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'write'45'reg_666
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2344
        -> coe (\ v2 v3 v4 v5 v6 v7 -> v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2346 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'write'45'reg_666
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2348 v2 v3
        -> coe (\ v4 v5 v6 v7 v8 v9 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2350 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  C_mkPtrBounds_446
                  (coe
                     (\ v9 ->
                        coe
                          du_go_1714 (coe v2) (coe v3) (coe v6) (coe v8) (coe v9)
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.du_readReg'45'write_484
                             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v9))))
                  (coe
                     (\ v9 ->
                        coe
                          du_pbm'45'ext_622
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498 v3 v9)
                          (coe d_pb'45'heap_438 v8 v9)))
                  (coe
                     (\ v9 v10 ->
                        coe
                          du_pbm'45'ext_622
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496 v3 v9 v10)
                          (coe d_pb'45'stack_444 v8 v9 v10))))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2352 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2354 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe du_pb'45'reg'45'op_1182 (coe v3) (coe v2) (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2356 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2358 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds._.st
d_st_1702 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_558 ->
  T_PBInv_412 -> Integer
d_st_1702 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 = du_st_1702 v3
du_st_1702 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 -> Integer
du_st_1702 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.bs
d_bs_1704 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_558 ->
  T_PBInv_412 -> Integer -> Integer
d_bs_1704 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 = du_bs_1704 v3
du_bs_1704 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> Integer
du_bs_1704 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.fresh
d_fresh_1706 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_558 ->
  T_PBInv_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fresh_1706 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 = du_fresh_1706 v3
du_fresh_1706 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_fresh_1706 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
               (coe du_st_1702 (coe v0)))
            (coe (0 :: Integer))))
-- Once.CCC.Machine.FlatPtrBounds._.fresh-ok
d_fresh'45'ok_1708 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_558 ->
  T_PBInv_412 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fresh'45'ok_1708 ~v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7
  = du_fresh'45'ok_1708 v1 v5
du_fresh'45'ok_1708 ::
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fresh'45'ok_1708 v0 v1 = coe v1 v0 erased
-- Once.CCC.Machine.FlatPtrBounds._.go
d_go_1714 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_558 ->
  T_PBInv_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_go_1714 ~v0 v1 v2 ~v3 ~v4 v5 ~v6 v7 v8 v9
  = du_go_1714 v1 v2 v5 v7 v8 v9
du_go_1714 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  T_PBInv_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_go_1714 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
        -> coe du_fresh'45'ok_1708 (coe v0) (coe v2)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> coe
             du_ptrb'45'ext_574
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v1))
                (coe v4))
             (coe d_pb'45'regs_434 v3 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-jump
d_pb'45'jump_1772 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_PBInv_412 -> T_PBInv_412
d_pb'45'jump_1772 ~v0 v1 ~v2 v3 = du_pb'45'jump_1772 v1 v3
du_pb'45'jump_1772 :: Maybe Integer -> T_PBInv_412 -> T_PBInv_412
du_pb'45'jump_1772 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatPtrBounds.pb-ret
d_pb'45'ret_1788 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_PBInv_412 -> T_PBInv_412
d_pb'45'ret_1788 ~v0 v1 ~v2 v3 = du_pb'45'ret_1788 v1 v3
du_pb'45'ret_1788 :: [Integer] -> T_PBInv_412 -> T_PBInv_412
du_pb'45'ret_1788 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatPtrBounds.pb-thunk
d_pb'45'thunk_1810 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_PBInv_412 -> T_PBInv_412
d_pb'45'thunk_1810 v0 v1 v2 v3
  = coe
      C_mkPtrBounds_446 (coe d_pb'45'regs_434 (coe v3))
      (coe d_pb'45'heap_438 (coe v3))
      (coe d_cleared_1826 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Machine.FlatPtrBounds._.cleared
d_cleared_1826 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_PBInv_412 -> AgdaAny -> Integer -> AgdaAny
d_cleared_1826 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__84 v0
              (coe
                 MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_102 v0
                 (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v2)))
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
                                    else coe seq (coe v11) (coe d_pb'45'stack_444 v3 v4 v5)
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   else coe seq (coe v9) (coe d_pb'45'stack_444 v3 v4 v5)
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.CCC.Machine.FlatPtrBounds.pb-branch
d_pb'45'branch_1856 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_PBInv_412 -> T_PBInv_412
d_pb'45'branch_1856 v0 v1 v2 v3 ~v4 v5
  = du_pb'45'branch_1856 v0 v1 v2 v3 v5
du_pb'45'branch_1856 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  T_PBInv_412 -> T_PBInv_412
du_pb'45'branch_1856 v0 v1 v2 v3 v4
  = if coe v1
      then coe
             du_pb'45'jump_1772
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v0)
                (coe v3) (coe v2))
             (coe v4)
      else coe v4
-- Once.CCC.Machine.FlatPtrBounds.pb-call
d_pb'45'call_1878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_PBInv_412 -> T_PBInv_412
d_pb'45'call_1878 v0 v1 v2 v3
  = coe
      du_go_1890 (coe v3)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_callView_942 (coe v0) (coe v1)
         (coe v2))
-- Once.CCC.Machine.FlatPtrBounds._.go
d_go_1890 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_PBInv_412 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_924 -> T_PBInv_412
d_go_1890 ~v0 ~v1 ~v2 v3 v4 = du_go_1890 v3 v4
du_go_1890 ::
  T_PBInv_412 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_924 -> T_PBInv_412
du_go_1890 v0 v1 = coe seq (coe v1) (coe v0)
-- Once.CCC.Machine.FlatPtrBounds.flat-ptr-bounds
d_flat'45'ptr'45'bounds_1918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_558 ->
  T_PBInv_412 -> T_PBInv_412
d_flat'45'ptr'45'bounds_1918 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2288
        -> coe
             du_pb'45'write'45'reg_666
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                d_pb'45'regs_434 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2290
        -> coe
             du_pb'45'write'45'reg_666
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
             (coe
                d_pb'45'regs_434 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2292
        -> coe
             du_pb'45'write'45'reg_666
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58)
             (coe
                d_pb'45'regs_434 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2294
        -> coe
             du_pb'45'write'45'reg_666
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                d_pb'45'regs_434 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2296
        -> coe
             du_pb'45'load'45'resolved_962
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1428
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3)))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2298
        -> coe
             du_pb'45'load'45'suc'45'resolved_990
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1428
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3)))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2300 v8
        -> coe
             du_pb'45'from'45'slot_1080
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3)))
                   (coe v8)))
             (coe
                du_pb'45'read'45'loc_902 (coe v7)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3)))
                   (coe v8)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2302 v8
        -> coe
             du_pb'45'write'45'mem_868 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3)))
                (coe v8))
             (coe
                d_pb'45'regs_434 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2304
        -> coe
             du_pb'45'store'45'resolved_1018 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1428
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3)))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                d_pb'45'regs_434 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2306
        -> coe
             du_pb'45'store'45'suc'45'resolved_1050 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1428
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3)))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                d_pb'45'regs_434 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2308 v8
        -> coe
             du_pb'45'write'45'reg_666
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2310 v8
        -> coe
             du_pb'45'restore_1106
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3)))
                   (coe v8)))
             (coe
                du_pb'45'read'45'loc_902 (coe v7)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3)))
                   (coe v8)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2316 v8
        -> coe v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2322
        -> coe d_pb'45'call_1878 (coe v0) (coe v2) (coe v3) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2324 v8
        -> coe v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2326 v8
        -> coe
             du_pb'45'write'45'mem_868 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3)))
                (coe v8))
             (coe
                d_pb'45'regs_434 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2328 v8
        -> coe
             du_pb'45'from'45'slot_1080
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3)))
                   (coe v8)))
             (coe
                du_pb'45'read'45'loc_902 (coe v7)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3)))
                   (coe v8)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2330 v8
        -> coe v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2336 v8 v9 v10
        -> coe
             du_pb'45'write'45'reg'45'halt_716
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                d_sigop'45'output'45'pb_1242 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2870
                         (coe v0) (coe v1)
                         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
                         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3)))))
                (coe v8) (coe v9) (coe v10)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2340 v8 v9 v10
        -> coe
             du_pb'45'write'45'reg_666
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2342 v8
        -> coe
             du_pb'45'write'45'reg_666
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2344
        -> coe v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2346 v8
        -> coe
             du_pb'45'write'45'reg_666
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2350 v8
        -> coe
             d_pb'45'abstract_1294 v0 v1
             (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v3)) v4 v5 v6
             v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2354 v8
        -> coe
             du_pb'45'reg'45'op_1182
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))
             (coe v8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2356 v8
        -> case coe v8 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2274 v9 -> coe v7
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2276 v9
               -> coe
                    du_pb'45'jump_1772
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v0)
                       (coe v2) (coe v9))
                    (coe v7)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2278 v9
               -> coe
                    du_pb'45'branch_1856 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_100
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3)))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)))
                    (coe v9) (coe v2) (coe v7)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2280 v9
               -> coe
                    du_pb'45'branch_1856 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_102
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_114
                          (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3))))
                    (coe v9) (coe v2) (coe v7)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2282 v9 v10
               -> coe d_pb'45'thunk_1810 (coe v0) (coe v10) (coe v3) (coe v7)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2284 v9
               -> coe
                    du_pb'45'ret_1788
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_86 (coe v3))
                    (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
