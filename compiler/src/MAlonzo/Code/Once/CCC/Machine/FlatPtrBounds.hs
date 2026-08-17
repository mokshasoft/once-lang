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
d_do'45'branch_190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'branch_190 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'branch_516 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.do-call
d_do'45'call_192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call_192 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call_918 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.do-jump
d_do'45'jump_200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'jump_200 ~v0 = du_do'45'jump_200
du_do'45'jump_200 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'jump_200
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_508
-- Once.CCC.Machine.FlatPtrBounds._.do-ret
d_do'45'ret_202 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'ret_202 ~v0 = du_do'45'ret_202
du_do'45'ret_202 ::
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'ret_202
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'ret_718
-- Once.CCC.Machine.FlatPtrBounds._.do-thunk
d_do'45'thunk_216 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'thunk_216 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'thunk_852 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.flat-exec-instr
d_flat'45'exec'45'instr_270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_270 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1080
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.falloc
d_falloc_368 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_falloc_368 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.fclosure
d_fclosure_370 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fclosure_370 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.flink
d_flink_372 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_372 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.floc
d_floc_374 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_floc_374 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.fpc
d_fpc_376 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_376 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.fret
d_fret_378 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_378 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF
d_StoreWF_396 a0 a1 a2 = ()
-- Once.CCC.Machine.FlatPtrBounds._.sv-below
d_sv'45'below_400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_sv'45'below_400 = erased
-- Once.CCC.Machine.FlatPtrBounds._.svm-below
d_svm'45'below_402 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_svm'45'below_402 = erased
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF.wf-fresh
d_wf'45'fresh_412 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_586 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wf'45'fresh_412 = erased
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF.wf-heap
d_wf'45'heap_414 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_586 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny
d_wf'45'heap_414 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'heap_616 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF.wf-regs
d_wf'45'regs_416 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_586 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
d_wf'45'regs_416 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'regs_612 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF.wf-stack
d_wf'45'stack_418 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_586 ->
  AgdaAny -> Integer -> AgdaAny
d_wf'45'stack_418 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'stack_622
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds.PtrB
d_PtrB_420 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_PtrB_420 = erased
-- Once.CCC.Machine.FlatPtrBounds.PtrB?
d_PtrB'63'_428 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_PtrB'63'_428 = erased
-- Once.CCC.Machine.FlatPtrBounds.PBInv
d_PBInv_440 a0 a1 a2 = ()
data T_PBInv_440
  = C_mkPtrBounds_474 (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
                       AgdaAny)
                      (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny)
                      (AgdaAny -> Integer -> AgdaAny)
-- Once.CCC.Machine.FlatPtrBounds.PBInv.pb-regs
d_pb'45'regs_462 ::
  T_PBInv_440 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
d_pb'45'regs_462 v0
  = case coe v0 of
      C_mkPtrBounds_474 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.PBInv.pb-heap
d_pb'45'heap_466 ::
  T_PBInv_440 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny
d_pb'45'heap_466 v0
  = case coe v0 of
      C_mkPtrBounds_474 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.PBInv.pb-stack
d_pb'45'stack_472 :: T_PBInv_440 -> AgdaAny -> Integer -> AgdaAny
d_pb'45'stack_472 v0
  = case coe v0 of
      C_mkPtrBounds_474 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.PtrBoundsWF
d_PtrBoundsWF_476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_PtrBoundsWF_476 = erased
-- Once.CCC.Machine.FlatPtrBounds.ptr-bounds-suc
d_ptr'45'bounds'45'suc_486 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_PBInv_440 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ptr'45'bounds'45'suc_486 ~v0 ~v1 v2 ~v3 v4 ~v5
  = du_ptr'45'bounds'45'suc_486 v2 v4
du_ptr'45'bounds'45'suc_486 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  T_PBInv_440 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ptr'45'bounds'45'suc_486 v0 v1 = coe d_pb'45'regs_462 v1 v0
-- Once.CCC.Machine.FlatPtrBounds.ptr-bounds-cell
d_ptr'45'bounds'45'cell_504 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_PBInv_440 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ptr'45'bounds'45'cell_504 ~v0 ~v1 v2 v3 v4 ~v5
  = du_ptr'45'bounds'45'cell_504 v2 v3 v4
du_ptr'45'bounds'45'cell_504 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_PBInv_440 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ptr'45'bounds'45'cell_504 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50
               (coe v1))))
      (coe du_ptr'45'bounds'45'suc_486 (coe v0) (coe v2))
-- Once.CCC.Machine.FlatPtrBounds.size-with-new
d_size'45'with'45'new_522 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_size'45'with'45'new_522 = erased
-- Once.CCC.Machine.FlatPtrBounds.size-with-old
d_size'45'with'45'old_556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_size'45'with'45'old_556 = erased
-- Once.CCC.Machine.FlatPtrBounds.ptrb-ext
d_ptrb'45'ext_602 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_ptrb'45'ext_602 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_ptrb'45'ext_602 v4 v6
du_ptrb'45'ext_602 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny
du_ptrb'45'ext_602 v0 v1
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
d_pbm'45'ext_650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_pbm'45'ext_650 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_pbm'45'ext_650 v4 v6
du_pbm'45'ext_650 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny
du_pbm'45'ext_650 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe du_ptrb'45'ext_602 (coe v2) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-halt
d_pb'45'halt_676 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Bool -> T_PBInv_440 -> T_PBInv_440
d_pb'45'halt_676 ~v0 ~v1 ~v2 ~v3 v4 = du_pb'45'halt_676 v4
du_pb'45'halt_676 :: T_PBInv_440 -> T_PBInv_440
du_pb'45'halt_676 v0 = coe v0
-- Once.CCC.Machine.FlatPtrBounds.pb-write-reg
d_pb'45'write'45'reg_694 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_440 -> T_PBInv_440
d_pb'45'write'45'reg_694 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'write'45'reg_694 v3 v5 v6
du_pb'45'write'45'reg_694 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> T_PBInv_440 -> T_PBInv_440
du_pb'45'write'45'reg_694 v0 v1 v2
  = coe
      C_mkPtrBounds_474
      (coe
         (\ v3 ->
            coe
              du_go_714 (coe v1) (coe v2) (coe v3)
              (coe
                 MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.du_readReg'45'write_512
                 (coe v0) (coe v3))))
      (coe d_pb'45'heap_466 (coe v2)) (coe d_pb'45'stack_472 (coe v2))
-- Once.CCC.Machine.FlatPtrBounds._.go
d_go_714 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny ->
  T_PBInv_440 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_go_714 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 = du_go_714 v5 v6 v7 v8
du_go_714 ::
  AgdaAny ->
  T_PBInv_440 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_go_714 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> coe d_pb'45'regs_462 v1 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-write-reg-halt
d_pb'45'write'45'reg'45'halt_744 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Bool -> AgdaAny -> T_PBInv_440 -> T_PBInv_440
d_pb'45'write'45'reg'45'halt_744 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du_pb'45'write'45'reg'45'halt_744 v3 v6 v7
du_pb'45'write'45'reg'45'halt_744 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> T_PBInv_440 -> T_PBInv_440
du_pb'45'write'45'reg'45'halt_744 v0 v1 v2
  = coe du_pb'45'write'45'reg_694 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.FlatPtrBounds.pb-wsm-aux
d_pb'45'wsm'45'aux_778 ::
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
d_pb'45'wsm'45'aux_778 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 v10
                       v11
  = du_pb'45'wsm'45'aux_778 v6 v7 v10 v11
du_pb'45'wsm'45'aux_778 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_pb'45'wsm'45'aux_778 v0 v1 v2 v3
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
d_pb'45'whm'45'aux_816 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_pb'45'whm'45'aux_816 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8
  = du_pb'45'whm'45'aux_816 v4 v7 v8
du_pb'45'whm'45'aux_816 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_pb'45'whm'45'aux_816 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe seq (coe v4) (coe v2)
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-write-stack
d_pb'45'write'45'stack_844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_440 -> T_PBInv_440
d_pb'45'write'45'stack_844 v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du_pb'45'write'45'stack_844 v0 v3 v4 v6 v7
du_pb'45'write'45'stack_844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> AgdaAny -> T_PBInv_440 -> T_PBInv_440
du_pb'45'write'45'stack_844 v0 v1 v2 v3 v4
  = coe
      C_mkPtrBounds_474 (coe d_pb'45'regs_462 (coe v4))
      (coe d_pb'45'heap_466 (coe v4))
      (coe
         (\ v5 v6 ->
            coe
              du_pb'45'wsm'45'aux_778
              (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__84 v0 v1 v5)
              (coe
                 MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v2) (coe v6))
              (coe d_pb'45'stack_472 v4 v5 v6) (coe v3)))
-- Once.CCC.Machine.FlatPtrBounds.pb-write-heap
d_pb'45'write'45'heap_872 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_440 -> T_PBInv_440
d_pb'45'write'45'heap_872 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'write'45'heap_872 v3 v5 v6
du_pb'45'write'45'heap_872 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> T_PBInv_440 -> T_PBInv_440
du_pb'45'write'45'heap_872 v0 v1 v2
  = coe
      C_mkPtrBounds_474 (coe d_pb'45'regs_462 (coe v2))
      (coe
         (\ v3 ->
            coe
              du_pb'45'whm'45'aux_816
              (coe
                 MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__80 (coe v0)
                 (coe v3))
              (coe d_pb'45'heap_466 v2 v3) (coe v1)))
      (coe d_pb'45'stack_472 (coe v2))
-- Once.CCC.Machine.FlatPtrBounds.pb-write-mem
d_pb'45'write'45'mem_896 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_440 -> T_PBInv_440
d_pb'45'write'45'mem_896 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'write'45'mem_896 v0 v3 v5 v6
du_pb'45'write'45'mem_896 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_PBInv_440 -> T_PBInv_440
du_pb'45'write'45'mem_896 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             du_pb'45'write'45'stack_844 (coe v0) (coe v4) (coe v5) (coe v2)
             (coe v3)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> coe du_pb'45'write'45'heap_872 (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-read-loc
d_pb'45'read'45'loc_930 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_PBInv_440 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
d_pb'45'read'45'loc_930 ~v0 ~v1 ~v2 v3 v4
  = du_pb'45'read'45'loc_930 v3 v4
du_pb'45'read'45'loc_930 ::
  T_PBInv_440 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
du_pb'45'read'45'loc_930 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe d_pb'45'stack_472 v0 v2 v3
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe d_pb'45'heap_466 v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-load-value
d_pb'45'load'45'value_958 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_440 -> T_PBInv_440
d_pb'45'load'45'value_958 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_pb'45'load'45'value_958 v3 v4 v5 v6
du_pb'45'load'45'value_958 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_440 -> T_PBInv_440
du_pb'45'load'45'value_958 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe du_pb'45'write'45'reg_694 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-load-resolved
d_pb'45'load'45'resolved_990 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_PBInv_440 -> T_PBInv_440
d_pb'45'load'45'resolved_990 ~v0 ~v1 v2 v3 v4 v5
  = du_pb'45'load'45'resolved_990 v2 v3 v4 v5
du_pb'45'load'45'resolved_990 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_PBInv_440 -> T_PBInv_440
du_pb'45'load'45'resolved_990 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_pb'45'load'45'value_958 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v0)
                (coe v4))
             (coe du_pb'45'read'45'loc_930 (coe v3) (coe v4)) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-load-suc-resolved
d_pb'45'load'45'suc'45'resolved_1018 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_PBInv_440 -> T_PBInv_440
d_pb'45'load'45'suc'45'resolved_1018 ~v0 ~v1 v2 v3 v4 v5
  = du_pb'45'load'45'suc'45'resolved_1018 v2 v3 v4 v5
du_pb'45'load'45'suc'45'resolved_1018 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_PBInv_440 -> T_PBInv_440
du_pb'45'load'45'suc'45'resolved_1018 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_pb'45'load'45'value_958 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v0)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v4)))
             (coe
                du_pb'45'read'45'loc_930 (coe v3)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v4)))
             (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-store-resolved
d_pb'45'store'45'resolved_1046 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_440 -> T_PBInv_440
d_pb'45'store'45'resolved_1046 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'store'45'resolved_1046 v0 v3 v5 v6
du_pb'45'store'45'resolved_1046 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_PBInv_440 -> T_PBInv_440
du_pb'45'store'45'resolved_1046 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_pb'45'write'45'mem_896 (coe v0) (coe v4) (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-store-suc-resolved
d_pb'45'store'45'suc'45'resolved_1078 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_440 -> T_PBInv_440
d_pb'45'store'45'suc'45'resolved_1078 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'store'45'suc'45'resolved_1078 v0 v3 v5 v6
du_pb'45'store'45'suc'45'resolved_1078 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_PBInv_440 -> T_PBInv_440
du_pb'45'store'45'suc'45'resolved_1078 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_pb'45'write'45'mem_896 (coe v0)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v4))
             (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-from-slot
d_pb'45'from'45'slot_1108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_440 -> T_PBInv_440
d_pb'45'from'45'slot_1108 ~v0 ~v1 ~v2 v3 v4 v5
  = du_pb'45'from'45'slot_1108 v3 v4 v5
du_pb'45'from'45'slot_1108 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_440 -> T_PBInv_440
du_pb'45'from'45'slot_1108 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_pb'45'write'45'reg_694
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v1)
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-restore
d_pb'45'restore_1134 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_440 -> T_PBInv_440
d_pb'45'restore_1134 ~v0 ~v1 ~v2 v3 v4 v5
  = du_pb'45'restore_1134 v3 v4 v5
du_pb'45'restore_1134 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_440 -> T_PBInv_440
du_pb'45'restore_1134 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_pb'45'write'45'reg_694
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v1)
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-pred
d_pb'45'pred_1158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
d_pb'45'pred_1158 ~v0 ~v1 v2 = du_pb'45'pred_1158 v2
du_pb'45'pred_1158 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
du_pb'45'pred_1158 v0
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
d_pb'45'succ_1184 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
d_pb'45'succ_1184 ~v0 ~v1 v2 = du_pb'45'succ_1184 v2
du_pb'45'succ_1184 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
du_pb'45'succ_1184 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatPtrBounds.pb-reg-op
d_pb'45'reg'45'op_1210 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_448 ->
  T_PBInv_440 -> T_PBInv_440
d_pb'45'reg'45'op_1210 ~v0 ~v1 v2 v3 v4
  = du_pb'45'reg'45'op_1210 v2 v3 v4
du_pb'45'reg'45'op_1210 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_448 ->
  T_PBInv_440 -> T_PBInv_440
du_pb'45'reg'45'op_1210 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_450
        -> coe
             du_pb'45'write'45'reg_694
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_452
        -> coe
             du_pb'45'write'45'reg_694
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_454
        -> coe
             du_pb'45'write'45'reg_694
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe
                du_pb'45'pred_1158
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v0))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)))
             (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_456
        -> coe
             du_pb'45'write'45'reg_694
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe
                d_pb'45'regs_462 v2
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64))
             (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_458
        -> coe
             du_pb'45'write'45'reg_694
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_460
        -> coe
             du_pb'45'write'45'reg_694
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64)
             (coe
                du_pb'45'succ_1184
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v0))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64)))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.structured-pure-sigop-inbounds
d_structured'45'pure'45'sigop'45'inbounds_1258
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.FlatPtrBounds.structured-pure-sigop-inbounds"
-- Once.CCC.Machine.FlatPtrBounds.sigop-output-pb
d_sigop'45'output'45'pb_1270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 -> AgdaAny
d_sigop'45'output'45'pb_1270 v0 v1 v2 v3 v4 v5
  = coe
      d_go_1312 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_212 (coe v4))
-- Once.CCC.Machine.FlatPtrBounds._.pov
d_pov_1290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 -> Maybe AgdaAny -> AgdaAny
d_pov_1290 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_pov_1290 v7
du_pov_1290 :: Maybe AgdaAny -> AgdaAny
du_pov_1290 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatPtrBounds._.aux
d_aux_1302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
d_aux_1302 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> coe
                    du_pov_1290
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2660 (coe v2)
                       (coe v9) (coe v5))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    du_pov_1290
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
             d_structured'45'pure'45'sigop'45'inbounds_1258 v0 v1 v2 v3 v4 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds._.go
d_go_1312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 -> AgdaAny
d_go_1312 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_124
        -> coe
             d_aux_1302 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
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
d_pb'45'abstract_1322 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_586 ->
  T_PBInv_440 -> T_PBInv_440
d_pb'45'abstract_1322 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2288
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'write'45'reg_694
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe
                     d_pb'45'regs_462 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2290
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'write'45'reg_694
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
                  (coe
                     d_pb'45'regs_462 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2292
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'write'45'reg_694
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58)
                  (coe
                     d_pb'45'regs_462 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2294
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'write'45'reg_694
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe
                     d_pb'45'regs_462 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2296
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'load'45'resolved_990 (coe v2)
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
                  du_pb'45'load'45'suc'45'resolved_1018 (coe v2)
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
                  du_pb'45'from'45'slot_1108
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v3)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                           (coe v4))
                        (coe v2)))
                  (coe
                     du_pb'45'read'45'loc_930 (coe v8)
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
                  du_pb'45'write'45'mem_896 (coe v0)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                        (coe v4))
                     (coe v2))
                  (coe
                     d_pb'45'regs_462 v8
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2304
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'store'45'resolved_1046 (coe v0)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1428
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                  (coe
                     d_pb'45'regs_462 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2306
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'store'45'suc'45'resolved_1078 (coe v0)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1428
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                  (coe
                     d_pb'45'regs_462 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2308 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'write'45'reg_694
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2310 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'restore_1134
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v3)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                           (coe v4))
                        (coe v2)))
                  (coe
                     du_pb'45'read'45'loc_930 (coe v8)
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
                  du_pb'45'write'45'mem_896 (coe v0)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                        (coe v4))
                     (coe v2))
                  (coe
                     d_pb'45'regs_462 v8
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2328 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'from'45'slot_1108
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v3)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                           (coe v4))
                        (coe v2)))
                  (coe
                     du_pb'45'read'45'loc_930 (coe v8)
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
                  du_pb'45'write'45'reg'45'halt_744
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe
                     d_sigop'45'output'45'pb_1270 (coe v0)
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
                  du_pb'45'write'45'reg_694
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v10))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2342 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'write'45'reg_694
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2344
        -> coe (\ v2 v3 v4 v5 v6 v7 -> v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2346 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'write'45'reg_694
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2348 v2 v3
        -> coe (\ v4 v5 v6 v7 v8 v9 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2350 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  C_mkPtrBounds_474
                  (coe
                     (\ v9 ->
                        coe
                          du_go_1742 (coe v2) (coe v3) (coe v6) (coe v8) (coe v9)
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.du_readReg'45'write_512
                             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v9))))
                  (coe
                     (\ v9 ->
                        coe
                          du_pbm'45'ext_650
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498 v3 v9)
                          (coe d_pb'45'heap_466 v8 v9)))
                  (coe
                     (\ v9 v10 ->
                        coe
                          du_pbm'45'ext_650
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496 v3 v9 v10)
                          (coe d_pb'45'stack_472 v8 v9 v10))))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2352 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2354 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe du_pb'45'reg'45'op_1210 (coe v3) (coe v2) (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2356 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2358 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds._.st
d_st_1730 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_586 ->
  T_PBInv_440 -> Integer
d_st_1730 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 = du_st_1730 v3
du_st_1730 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 -> Integer
du_st_1730 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.bs
d_bs_1732 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_586 ->
  T_PBInv_440 -> Integer -> Integer
d_bs_1732 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 = du_bs_1732 v3
du_bs_1732 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> Integer
du_bs_1732 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.fresh
d_fresh_1734 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_586 ->
  T_PBInv_440 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fresh_1734 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 = du_fresh_1734 v3
du_fresh_1734 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_fresh_1734 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
               (coe du_st_1730 (coe v0)))
            (coe (0 :: Integer))))
-- Once.CCC.Machine.FlatPtrBounds._.fresh-ok
d_fresh'45'ok_1736 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_586 ->
  T_PBInv_440 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fresh'45'ok_1736 ~v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7
  = du_fresh'45'ok_1736 v1 v5
du_fresh'45'ok_1736 ::
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fresh'45'ok_1736 v0 v1 = coe v1 v0 erased
-- Once.CCC.Machine.FlatPtrBounds._.go
d_go_1742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_586 ->
  T_PBInv_440 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_go_1742 ~v0 v1 v2 ~v3 ~v4 v5 ~v6 v7 v8 v9
  = du_go_1742 v1 v2 v5 v7 v8 v9
du_go_1742 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  T_PBInv_440 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_go_1742 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
        -> coe du_fresh'45'ok_1736 (coe v0) (coe v2)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> coe
             du_ptrb'45'ext_602
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v1))
                (coe v4))
             (coe d_pb'45'regs_462 v3 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-jump
d_pb'45'jump_1800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_PBInv_440 -> T_PBInv_440
d_pb'45'jump_1800 ~v0 v1 ~v2 v3 = du_pb'45'jump_1800 v1 v3
du_pb'45'jump_1800 :: Maybe Integer -> T_PBInv_440 -> T_PBInv_440
du_pb'45'jump_1800 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatPtrBounds.pb-ret
d_pb'45'ret_1816 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_PBInv_440 -> T_PBInv_440
d_pb'45'ret_1816 ~v0 v1 ~v2 v3 = du_pb'45'ret_1816 v1 v3
du_pb'45'ret_1816 :: [Integer] -> T_PBInv_440 -> T_PBInv_440
du_pb'45'ret_1816 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatPtrBounds.pb-thunk
d_pb'45'thunk_1838 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_PBInv_440 -> T_PBInv_440
d_pb'45'thunk_1838 v0 v1 v2 v3
  = coe
      C_mkPtrBounds_474 (coe d_pb'45'regs_462 (coe v3))
      (coe d_pb'45'heap_466 (coe v3))
      (coe d_cleared_1854 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Machine.FlatPtrBounds._.cleared
d_cleared_1854 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_PBInv_440 -> AgdaAny -> Integer -> AgdaAny
d_cleared_1854 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__84 v0
              (coe
                 MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_102 v0
                 (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
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
                                    else coe seq (coe v11) (coe d_pb'45'stack_472 v3 v4 v5)
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   else coe seq (coe v9) (coe d_pb'45'stack_472 v3 v4 v5)
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.CCC.Machine.FlatPtrBounds.pb-branch
d_pb'45'branch_1884 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_PBInv_440 -> T_PBInv_440
d_pb'45'branch_1884 v0 v1 v2 v3 ~v4 v5
  = du_pb'45'branch_1884 v0 v1 v2 v3 v5
du_pb'45'branch_1884 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  T_PBInv_440 -> T_PBInv_440
du_pb'45'branch_1884 v0 v1 v2 v3 v4
  = if coe v1
      then coe
             du_pb'45'jump_1800
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
                (coe v3) (coe v2))
             (coe v4)
      else coe v4
-- Once.CCC.Machine.FlatPtrBounds.pb-call
d_pb'45'call_1906 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_PBInv_440 -> T_PBInv_440
d_pb'45'call_1906 v0 v1 v2 v3
  = coe
      du_go_1918 (coe v3)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_callView_946 (coe v0) (coe v1)
         (coe v2))
-- Once.CCC.Machine.FlatPtrBounds._.go
d_go_1918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_PBInv_440 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_928 -> T_PBInv_440
d_go_1918 ~v0 ~v1 ~v2 v3 v4 = du_go_1918 v3 v4
du_go_1918 ::
  T_PBInv_440 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_928 -> T_PBInv_440
du_go_1918 v0 v1 = coe seq (coe v1) (coe v0)
-- Once.CCC.Machine.FlatPtrBounds.flat-ptr-bounds
d_flat'45'ptr'45'bounds_1946 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_586 ->
  T_PBInv_440 -> T_PBInv_440
d_flat'45'ptr'45'bounds_1946 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2288
        -> coe
             du_pb'45'write'45'reg_694
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                d_pb'45'regs_462 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2290
        -> coe
             du_pb'45'write'45'reg_694
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
             (coe
                d_pb'45'regs_462 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2292
        -> coe
             du_pb'45'write'45'reg_694
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58)
             (coe
                d_pb'45'regs_462 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2294
        -> coe
             du_pb'45'write'45'reg_694
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                d_pb'45'regs_462 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2296
        -> coe
             du_pb'45'load'45'resolved_990
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1428
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3)))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2298
        -> coe
             du_pb'45'load'45'suc'45'resolved_1018
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1428
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3)))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2300 v8
        -> coe
             du_pb'45'from'45'slot_1108
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)))
                   (coe v8)))
             (coe
                du_pb'45'read'45'loc_930 (coe v7)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)))
                   (coe v8)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2302 v8
        -> coe
             du_pb'45'write'45'mem_896 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)))
                (coe v8))
             (coe
                d_pb'45'regs_462 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2304
        -> coe
             du_pb'45'store'45'resolved_1046 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1428
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3)))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                d_pb'45'regs_462 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2306
        -> coe
             du_pb'45'store'45'suc'45'resolved_1078 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1428
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3)))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                d_pb'45'regs_462 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2308 v8
        -> coe
             du_pb'45'write'45'reg_694
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2310 v8
        -> coe
             du_pb'45'restore_1134
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)))
                   (coe v8)))
             (coe
                du_pb'45'read'45'loc_930 (coe v7)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)))
                   (coe v8)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2316 v8
        -> coe v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2322
        -> coe d_pb'45'call_1906 (coe v0) (coe v2) (coe v3) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2324 v8
        -> coe v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2326 v8
        -> coe
             du_pb'45'write'45'mem_896 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)))
                (coe v8))
             (coe
                d_pb'45'regs_462 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2328 v8
        -> coe
             du_pb'45'from'45'slot_1108
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)))
                   (coe v8)))
             (coe
                du_pb'45'read'45'loc_930 (coe v7)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)))
                   (coe v8)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2330 v8
        -> coe v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2336 v8 v9 v10
        -> coe
             du_pb'45'write'45'reg'45'halt_744
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                d_sigop'45'output'45'pb_1270 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2870
                         (coe v0) (coe v1)
                         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)))))
                (coe v8) (coe v9) (coe v10)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2340 v8 v9 v10
        -> coe
             du_pb'45'write'45'reg_694
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2342 v8
        -> coe
             du_pb'45'write'45'reg_694
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2344
        -> coe v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2346 v8
        -> coe
             du_pb'45'write'45'reg_694
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2350 v8
        -> coe
             d_pb'45'abstract_1322 v0 v1
             (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)) v4 v5 v6
             v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2354 v8
        -> coe
             du_pb'45'reg'45'op_1210
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe v8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2356 v8
        -> case coe v8 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2274 v9 -> coe v7
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2276 v9
               -> coe
                    du_pb'45'jump_1800
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
                       (coe v2) (coe v9))
                    (coe v7)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2278 v9
               -> coe
                    du_pb'45'branch_1884 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_104
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3)))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)))
                    (coe v9) (coe v2) (coe v7)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2280 v9
               -> coe
                    du_pb'45'branch_1884 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_106
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_118
                          (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))))
                    (coe v9) (coe v2) (coe v7)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2282 v9 v10
               -> coe d_pb'45'thunk_1838 (coe v0) (coe v10) (coe v3) (coe v7)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2284 v9
               -> coe
                    du_pb'45'ret_1816
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v3))
                    (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
