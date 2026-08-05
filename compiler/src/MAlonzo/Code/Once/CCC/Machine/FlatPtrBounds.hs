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
d_readLoc_20 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_readLoc_20 ~v0 = du_readLoc_20
du_readLoc_20 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_readLoc_20
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712
-- Once.CCC.Machine.FlatPtrBounds._.writeHeapMem-aux
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem'45'aux_758 v2
      v3 v4
-- Once.CCC.Machine.FlatPtrBounds._.writeLoc
d_writeLoc_28 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_writeLoc_28 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_792 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.writeLocToHeap
d_writeLocToHeap_44 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_writeLocToHeap_44 ~v0 = du_writeLocToHeap_44
du_writeLocToHeap_44 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_writeLocToHeap_44
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_784
-- Once.CCC.Machine.FlatPtrBounds._.writeLocToStack
d_writeLocToStack_46 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_writeLocToStack_46 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLocToStack_774 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.writeStackMem-aux
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeStackMem'45'aux_732 v4
      v5 v6 v7
-- Once.CCC.Machine.FlatPtrBounds._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_62 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'load'45'suc'45'via'45'resolved_62 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_62
du_exec'45'load'45'suc'45'via'45'resolved_62 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_exec'45'load'45'suc'45'via'45'resolved_62
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'suc'45'via'45'resolved_1478
-- Once.CCC.Machine.FlatPtrBounds._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_64 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'load'45'via'45'resolved_64 ~v0
  = du_exec'45'load'45'via'45'resolved_64
du_exec'45'load'45'via'45'resolved_64 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_exec'45'load'45'via'45'resolved_64
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'via'45'resolved_1440
-- Once.CCC.Machine.FlatPtrBounds._.exec-load-with-value
d_exec'45'load'45'with'45'value_66 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'load'45'with'45'value_66 ~v0
  = du_exec'45'load'45'with'45'value_66
du_exec'45'load'45'with'45'value_66 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_exec'45'load'45'with'45'value_66
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'with'45'value_1428
-- Once.CCC.Machine.FlatPtrBounds._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_68 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'store'45'suc'45'via'45'resolved_68 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'suc'45'via'45'resolved_1490
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_70 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'store'45'via'45'resolved_70 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'via'45'resolved_1452
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.exec-abstract
d_exec'45'abstract_86 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_86 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2766
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_96 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_96 ~v0
  = du_exec'45'load'45'from'45'slot'45'with'45'value_96
du_exec'45'load'45'from'45'slot'45'with'45'value_96 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_96
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'from'45'slot'45'with'45'value_2462
-- Once.CCC.Machine.FlatPtrBounds._.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_106 ~v0
  = du_exec'45'restore'45'input'45'with'45'value_106
du_exec'45'restore'45'input'45'with'45'value_106 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_106
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'restore'45'input'45'with'45'value_2474
-- Once.CCC.Machine.FlatPtrBounds._.exec-sigop-output
d_exec'45'sigop'45'output_112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_exec'45'sigop'45'output_112 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output_2660
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_114 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_exec'45'sigop'45'output'45'of_114 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output'45'of_2650
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_146 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_pure'45'sigop'45'out'45'aux_146 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'aux_2614
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.pure-sigop-out-val
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_pure'45'sigop'45'out'45'val_2598
      v1 v2 v3 v4
-- Once.CCC.Machine.FlatPtrBounds._.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_structured'45'pure'45'sigop'45'output_160 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_structured'45'pure'45'sigop'45'output_2586
      v0
-- Once.CCC.Machine.FlatPtrBounds._.FlatState
d_FlatState_166 a0 = ()
-- Once.CCC.Machine.FlatPtrBounds._.do-branch
d_do'45'branch_174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_do'45'branch_174 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'branch_232 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.do-jump
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
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_224
-- Once.CCC.Machine.FlatPtrBounds._.do-ret
d_do'45'ret_178 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_do'45'ret_178 ~v0 = du_do'45'ret_178
du_do'45'ret_178 ::
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_do'45'ret_178
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'ret_430
-- Once.CCC.Machine.FlatPtrBounds._.flat-exec-instr
d_flat'45'exec'45'instr_234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_flat'45'exec'45'instr_234 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_570
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.falloc
d_falloc_298 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_falloc_298 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.fclosure
d_fclosure_300 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fclosure_300 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_82 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.floc
d_floc_302 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_floc_302 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.fpc
d_fpc_304 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> Integer
d_fpc_304 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.fret
d_fret_306 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> [Integer]
d_fret_306 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF
d_StoreWF_316 a0 a1 a2 = ()
-- Once.CCC.Machine.FlatPtrBounds._.sv-below
d_sv'45'below_320 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_sv'45'below_320 = erased
-- Once.CCC.Machine.FlatPtrBounds._.svm-below
d_svm'45'below_322 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_svm'45'below_322 = erased
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF.wf-fresh
d_wf'45'fresh_332 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wf'45'fresh_332 = erased
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF.wf-heap
d_wf'45'heap_334 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny
d_wf'45'heap_334 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'heap_536 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF.wf-regs
d_wf'45'regs_336 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
d_wf'45'regs_336 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'regs_532 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF.wf-stack
d_wf'45'stack_338 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506 ->
  AgdaAny -> Integer -> AgdaAny
d_wf'45'stack_338 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'stack_542
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds.PtrB
d_PtrB_340 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_PtrB_340 = erased
-- Once.CCC.Machine.FlatPtrBounds.PtrB?
d_PtrB'63'_348 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_PtrB'63'_348 = erased
-- Once.CCC.Machine.FlatPtrBounds.PBInv
d_PBInv_360 a0 a1 a2 = ()
data T_PBInv_360
  = C_mkPtrBounds_394 (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
                       AgdaAny)
                      (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny)
                      (AgdaAny -> Integer -> AgdaAny)
-- Once.CCC.Machine.FlatPtrBounds.PBInv.pb-regs
d_pb'45'regs_382 ::
  T_PBInv_360 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
d_pb'45'regs_382 v0
  = case coe v0 of
      C_mkPtrBounds_394 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.PBInv.pb-heap
d_pb'45'heap_386 ::
  T_PBInv_360 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny
d_pb'45'heap_386 v0
  = case coe v0 of
      C_mkPtrBounds_394 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.PBInv.pb-stack
d_pb'45'stack_392 :: T_PBInv_360 -> AgdaAny -> Integer -> AgdaAny
d_pb'45'stack_392 v0
  = case coe v0 of
      C_mkPtrBounds_394 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.PtrBoundsWF
d_PtrBoundsWF_396 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_PtrBoundsWF_396 = erased
-- Once.CCC.Machine.FlatPtrBounds.ptr-bounds-suc
d_ptr'45'bounds'45'suc_406 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_PBInv_360 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ptr'45'bounds'45'suc_406 ~v0 ~v1 v2 ~v3 v4 ~v5
  = du_ptr'45'bounds'45'suc_406 v2 v4
du_ptr'45'bounds'45'suc_406 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  T_PBInv_360 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ptr'45'bounds'45'suc_406 v0 v1 = coe d_pb'45'regs_382 v1 v0
-- Once.CCC.Machine.FlatPtrBounds.ptr-bounds-cell
d_ptr'45'bounds'45'cell_424 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_PBInv_360 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ptr'45'bounds'45'cell_424 ~v0 ~v1 v2 v3 v4 ~v5
  = du_ptr'45'bounds'45'cell_424 v2 v3 v4
du_ptr'45'bounds'45'cell_424 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_PBInv_360 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ptr'45'bounds'45'cell_424 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50
               (coe v1))))
      (coe du_ptr'45'bounds'45'suc_406 (coe v0) (coe v2))
-- Once.CCC.Machine.FlatPtrBounds.size-with-new
d_size'45'with'45'new_442 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_size'45'with'45'new_442 = erased
-- Once.CCC.Machine.FlatPtrBounds.size-with-old
d_size'45'with'45'old_476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_size'45'with'45'old_476 = erased
-- Once.CCC.Machine.FlatPtrBounds.ptrb-ext
d_ptrb'45'ext_522 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_ptrb'45'ext_522 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_ptrb'45'ext_522 v4 v6
du_ptrb'45'ext_522 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny
du_ptrb'45'ext_522 v0 v1
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
d_pbm'45'ext_570 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_pbm'45'ext_570 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_pbm'45'ext_570 v4 v6
du_pbm'45'ext_570 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny
du_pbm'45'ext_570 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe du_ptrb'45'ext_522 (coe v2) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-halt
d_pb'45'halt_596 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Bool -> T_PBInv_360 -> T_PBInv_360
d_pb'45'halt_596 ~v0 ~v1 ~v2 ~v3 v4 = du_pb'45'halt_596 v4
du_pb'45'halt_596 :: T_PBInv_360 -> T_PBInv_360
du_pb'45'halt_596 v0 = coe v0
-- Once.CCC.Machine.FlatPtrBounds.pb-write-reg
d_pb'45'write'45'reg_614 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_360 -> T_PBInv_360
d_pb'45'write'45'reg_614 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'write'45'reg_614 v3 v5 v6
du_pb'45'write'45'reg_614 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> T_PBInv_360 -> T_PBInv_360
du_pb'45'write'45'reg_614 v0 v1 v2
  = coe
      C_mkPtrBounds_394
      (coe
         (\ v3 ->
            coe
              du_go_634 (coe v1) (coe v2) (coe v3)
              (coe
                 MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.du_readReg'45'write_432
                 (coe v0) (coe v3))))
      (coe d_pb'45'heap_386 (coe v2)) (coe d_pb'45'stack_392 (coe v2))
-- Once.CCC.Machine.FlatPtrBounds._.go
d_go_634 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny ->
  T_PBInv_360 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_go_634 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 = du_go_634 v5 v6 v7 v8
du_go_634 ::
  AgdaAny ->
  T_PBInv_360 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_go_634 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> coe d_pb'45'regs_382 v1 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-write-reg-halt
d_pb'45'write'45'reg'45'halt_664 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Bool -> AgdaAny -> T_PBInv_360 -> T_PBInv_360
d_pb'45'write'45'reg'45'halt_664 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du_pb'45'write'45'reg'45'halt_664 v3 v6 v7
du_pb'45'write'45'reg'45'halt_664 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> T_PBInv_360 -> T_PBInv_360
du_pb'45'write'45'reg'45'halt_664 v0 v1 v2
  = coe du_pb'45'write'45'reg_614 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.FlatPtrBounds.pb-wsm-aux
d_pb'45'wsm'45'aux_698 ::
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
d_pb'45'wsm'45'aux_698 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 v10
                       v11
  = du_pb'45'wsm'45'aux_698 v6 v7 v10 v11
du_pb'45'wsm'45'aux_698 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_pb'45'wsm'45'aux_698 v0 v1 v2 v3
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
d_pb'45'whm'45'aux_736 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_pb'45'whm'45'aux_736 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8
  = du_pb'45'whm'45'aux_736 v4 v7 v8
du_pb'45'whm'45'aux_736 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_pb'45'whm'45'aux_736 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe seq (coe v4) (coe v2)
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-write-stack
d_pb'45'write'45'stack_764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_360 -> T_PBInv_360
d_pb'45'write'45'stack_764 v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du_pb'45'write'45'stack_764 v0 v3 v4 v6 v7
du_pb'45'write'45'stack_764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> AgdaAny -> T_PBInv_360 -> T_PBInv_360
du_pb'45'write'45'stack_764 v0 v1 v2 v3 v4
  = coe
      C_mkPtrBounds_394 (coe d_pb'45'regs_382 (coe v4))
      (coe d_pb'45'heap_386 (coe v4))
      (coe
         (\ v5 v6 ->
            coe
              du_pb'45'wsm'45'aux_698
              (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__84 v0 v1 v5)
              (coe
                 MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v2) (coe v6))
              (coe d_pb'45'stack_392 v4 v5 v6) (coe v3)))
-- Once.CCC.Machine.FlatPtrBounds.pb-write-heap
d_pb'45'write'45'heap_792 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_360 -> T_PBInv_360
d_pb'45'write'45'heap_792 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'write'45'heap_792 v3 v5 v6
du_pb'45'write'45'heap_792 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> T_PBInv_360 -> T_PBInv_360
du_pb'45'write'45'heap_792 v0 v1 v2
  = coe
      C_mkPtrBounds_394 (coe d_pb'45'regs_382 (coe v2))
      (coe
         (\ v3 ->
            coe
              du_pb'45'whm'45'aux_736
              (coe
                 MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__80 (coe v0)
                 (coe v3))
              (coe d_pb'45'heap_386 v2 v3) (coe v1)))
      (coe d_pb'45'stack_392 (coe v2))
-- Once.CCC.Machine.FlatPtrBounds.pb-write-mem
d_pb'45'write'45'mem_816 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_360 -> T_PBInv_360
d_pb'45'write'45'mem_816 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'write'45'mem_816 v0 v3 v5 v6
du_pb'45'write'45'mem_816 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_PBInv_360 -> T_PBInv_360
du_pb'45'write'45'mem_816 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             du_pb'45'write'45'stack_764 (coe v0) (coe v4) (coe v5) (coe v2)
             (coe v3)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> coe du_pb'45'write'45'heap_792 (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-read-loc
d_pb'45'read'45'loc_850 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_PBInv_360 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
d_pb'45'read'45'loc_850 ~v0 ~v1 ~v2 v3 v4
  = du_pb'45'read'45'loc_850 v3 v4
du_pb'45'read'45'loc_850 ::
  T_PBInv_360 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
du_pb'45'read'45'loc_850 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe d_pb'45'stack_392 v0 v2 v3
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe d_pb'45'heap_386 v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-load-value
d_pb'45'load'45'value_878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_360 -> T_PBInv_360
d_pb'45'load'45'value_878 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_pb'45'load'45'value_878 v3 v4 v5 v6
du_pb'45'load'45'value_878 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_360 -> T_PBInv_360
du_pb'45'load'45'value_878 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe du_pb'45'write'45'reg_614 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-load-resolved
d_pb'45'load'45'resolved_910 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_PBInv_360 -> T_PBInv_360
d_pb'45'load'45'resolved_910 ~v0 ~v1 v2 v3 v4 v5
  = du_pb'45'load'45'resolved_910 v2 v3 v4 v5
du_pb'45'load'45'resolved_910 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_PBInv_360 -> T_PBInv_360
du_pb'45'load'45'resolved_910 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_pb'45'load'45'value_878 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v0)
                (coe v4))
             (coe du_pb'45'read'45'loc_850 (coe v3) (coe v4)) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-load-suc-resolved
d_pb'45'load'45'suc'45'resolved_938 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_PBInv_360 -> T_PBInv_360
d_pb'45'load'45'suc'45'resolved_938 ~v0 ~v1 v2 v3 v4 v5
  = du_pb'45'load'45'suc'45'resolved_938 v2 v3 v4 v5
du_pb'45'load'45'suc'45'resolved_938 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_PBInv_360 -> T_PBInv_360
du_pb'45'load'45'suc'45'resolved_938 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_pb'45'load'45'value_878 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v0)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v4)))
             (coe
                du_pb'45'read'45'loc_850 (coe v3)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v4)))
             (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-store-resolved
d_pb'45'store'45'resolved_966 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_360 -> T_PBInv_360
d_pb'45'store'45'resolved_966 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'store'45'resolved_966 v0 v3 v5 v6
du_pb'45'store'45'resolved_966 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_PBInv_360 -> T_PBInv_360
du_pb'45'store'45'resolved_966 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_pb'45'write'45'mem_816 (coe v0) (coe v4) (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-store-suc-resolved
d_pb'45'store'45'suc'45'resolved_998 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_360 -> T_PBInv_360
d_pb'45'store'45'suc'45'resolved_998 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'store'45'suc'45'resolved_998 v0 v3 v5 v6
du_pb'45'store'45'suc'45'resolved_998 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_PBInv_360 -> T_PBInv_360
du_pb'45'store'45'suc'45'resolved_998 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_pb'45'write'45'mem_816 (coe v0)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v4))
             (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-from-slot
d_pb'45'from'45'slot_1028 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_360 -> T_PBInv_360
d_pb'45'from'45'slot_1028 ~v0 ~v1 ~v2 v3 v4 v5
  = du_pb'45'from'45'slot_1028 v3 v4 v5
du_pb'45'from'45'slot_1028 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_360 -> T_PBInv_360
du_pb'45'from'45'slot_1028 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_pb'45'write'45'reg_614
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v1)
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-restore
d_pb'45'restore_1054 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_360 -> T_PBInv_360
d_pb'45'restore_1054 ~v0 ~v1 ~v2 v3 v4 v5
  = du_pb'45'restore_1054 v3 v4 v5
du_pb'45'restore_1054 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_360 -> T_PBInv_360
du_pb'45'restore_1054 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_pb'45'write'45'reg_614
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v1)
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-pred
d_pb'45'pred_1078 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
d_pb'45'pred_1078 ~v0 ~v1 v2 = du_pb'45'pred_1078 v2
du_pb'45'pred_1078 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
du_pb'45'pred_1078 v0
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
d_pb'45'succ_1104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
d_pb'45'succ_1104 ~v0 ~v1 v2 = du_pb'45'succ_1104 v2
du_pb'45'succ_1104 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
du_pb'45'succ_1104 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatPtrBounds.pb-reg-op
d_pb'45'reg'45'op_1130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_448 ->
  T_PBInv_360 -> T_PBInv_360
d_pb'45'reg'45'op_1130 ~v0 ~v1 v2 v3 v4
  = du_pb'45'reg'45'op_1130 v2 v3 v4
du_pb'45'reg'45'op_1130 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_448 ->
  T_PBInv_360 -> T_PBInv_360
du_pb'45'reg'45'op_1130 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_450
        -> coe
             du_pb'45'write'45'reg_614
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_452
        -> coe
             du_pb'45'write'45'reg_614
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_454
        -> coe
             du_pb'45'write'45'reg_614
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe
                du_pb'45'pred_1078
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v0))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)))
             (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_456
        -> coe
             du_pb'45'write'45'reg_614
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe
                d_pb'45'regs_382 v2
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64))
             (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_458
        -> coe
             du_pb'45'write'45'reg_614
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_460
        -> coe
             du_pb'45'write'45'reg_614
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64)
             (coe
                du_pb'45'succ_1104
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v0))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64)))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.structured-pure-sigop-inbounds
d_structured'45'pure'45'sigop'45'inbounds_1178
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.FlatPtrBounds.structured-pure-sigop-inbounds"
-- Once.CCC.Machine.FlatPtrBounds.sigop-output-pb
d_sigop'45'output'45'pb_1190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 -> AgdaAny
d_sigop'45'output'45'pb_1190 v0 v1 v2 v3 v4 v5
  = coe
      d_go_1232 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_212 (coe v4))
-- Once.CCC.Machine.FlatPtrBounds._.pov
d_pov_1210 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 -> Maybe AgdaAny -> AgdaAny
d_pov_1210 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_pov_1210 v7
du_pov_1210 :: Maybe AgdaAny -> AgdaAny
du_pov_1210 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatPtrBounds._.aux
d_aux_1222 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
d_aux_1222 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> coe
                    du_pov_1210
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2556 (coe v2)
                       (coe v9) (coe v5))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    du_pov_1210
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg'45'typed_2550
                       (coe v2)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v5))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             d_structured'45'pure'45'sigop'45'inbounds_1178 v0 v1 v2 v3 v4 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds._.go
d_go_1232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 -> AgdaAny
d_go_1232 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_124
        -> coe
             d_aux_1222 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_204 (coe v3))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1342
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
d_pb'45'abstract_1242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506 ->
  T_PBInv_360 -> T_PBInv_360
d_pb'45'abstract_1242 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'write'45'reg_614
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe
                     d_pb'45'regs_382 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'write'45'reg_614
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
                  (coe
                     d_pb'45'regs_382 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2194
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'write'45'reg_614
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58)
                  (coe
                     d_pb'45'regs_382 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2196
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'write'45'reg_614
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe
                     d_pb'45'regs_382 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'load'45'resolved_910 (coe v2)
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1342
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'load'45'suc'45'resolved_938 (coe v2)
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1342
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'from'45'slot_1028
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v3)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                           (coe v4))
                        (coe v2)))
                  (coe
                     du_pb'45'read'45'loc_850 (coe v8)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                           (coe v4))
                        (coe v2)))
                  (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'write'45'mem_816 (coe v0)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                        (coe v4))
                     (coe v2))
                  (coe
                     d_pb'45'regs_382 v8
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'store'45'resolved_966 (coe v0)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1342
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                  (coe
                     d_pb'45'regs_382 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'store'45'suc'45'resolved_998 (coe v0)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1342
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                  (coe
                     d_pb'45'regs_382 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2210 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'write'45'reg_614
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2212 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'restore_1054
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v3)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                           (coe v4))
                        (coe v2)))
                  (coe
                     du_pb'45'read'45'loc_850 (coe v8)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                           (coe v4))
                        (coe v2)))
                  (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2214 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2216 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2218 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2220 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2222
        -> coe (\ v2 v3 v4 v5 v6 v7 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2224
        -> coe (\ v2 v3 v4 v5 v6 v7 -> v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2226 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2228 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'write'45'mem_816 (coe v0)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                        (coe v4))
                     (coe v2))
                  (coe
                     d_pb'45'regs_382 v8
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2230 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'from'45'slot_1028
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v3)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                           (coe v4))
                        (coe v2)))
                  (coe
                     du_pb'45'read'45'loc_850 (coe v8)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                           (coe v4))
                        (coe v2)))
                  (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2232 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2238 v2 v3 v4
        -> coe
             (\ v5 v6 v7 v8 v9 v10 ->
                coe
                  du_pb'45'write'45'reg'45'halt_664
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe
                     d_sigop'45'output'45'pb_1190 (coe v0)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2766
                              (coe v0) (coe v1) (coe v5) (coe v6))))
                     (coe v2) (coe v3) (coe v4) (coe v5))
                  (coe v10))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2242 v2 v3 v4
        -> coe
             (\ v5 v6 v7 v8 v9 v10 ->
                coe
                  du_pb'45'write'45'reg_614
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v10))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2244 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'write'45'reg_614
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2246
        -> coe (\ v2 v3 v4 v5 v6 v7 -> v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2248 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'write'45'reg_614
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2250 v2 v3
        -> coe (\ v4 v5 v6 v7 v8 v9 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  C_mkPtrBounds_394
                  (coe
                     (\ v9 ->
                        coe
                          du_go_1662 (coe v2) (coe v3) (coe v6) (coe v8) (coe v9)
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.du_readReg'45'write_432
                             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v9))))
                  (coe
                     (\ v9 ->
                        coe
                          du_pbm'45'ext_570
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498 v3 v9)
                          (coe d_pb'45'heap_386 v8 v9)))
                  (coe
                     (\ v9 v10 ->
                        coe
                          du_pbm'45'ext_570
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496 v3 v9 v10)
                          (coe d_pb'45'stack_392 v8 v9 v10))))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2254 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe du_pb'45'reg'45'op_1130 (coe v3) (coe v2) (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2260 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds._.st
d_st_1650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506 ->
  T_PBInv_360 -> Integer
d_st_1650 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 = du_st_1650 v3
du_st_1650 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 -> Integer
du_st_1650 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.bs
d_bs_1652 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506 ->
  T_PBInv_360 -> Integer -> Integer
d_bs_1652 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 = du_bs_1652 v3
du_bs_1652 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> Integer
du_bs_1652 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.fresh
d_fresh_1654 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506 ->
  T_PBInv_360 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fresh_1654 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 = du_fresh_1654 v3
du_fresh_1654 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_fresh_1654 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
               (coe du_st_1650 (coe v0)))
            (coe (0 :: Integer))))
-- Once.CCC.Machine.FlatPtrBounds._.fresh-ok
d_fresh'45'ok_1656 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506 ->
  T_PBInv_360 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fresh'45'ok_1656 ~v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7
  = du_fresh'45'ok_1656 v1 v5
du_fresh'45'ok_1656 ::
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fresh'45'ok_1656 v0 v1 = coe v1 v0 erased
-- Once.CCC.Machine.FlatPtrBounds._.go
d_go_1662 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506 ->
  T_PBInv_360 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_go_1662 ~v0 v1 v2 ~v3 ~v4 v5 ~v6 v7 v8 v9
  = du_go_1662 v1 v2 v5 v7 v8 v9
du_go_1662 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  T_PBInv_360 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_go_1662 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
        -> coe du_fresh'45'ok_1656 (coe v0) (coe v2)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> coe
             du_ptrb'45'ext_522
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v1))
                (coe v4))
             (coe d_pb'45'regs_382 v3 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-jump
d_pb'45'jump_1720 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_PBInv_360 -> T_PBInv_360
d_pb'45'jump_1720 ~v0 v1 ~v2 v3 = du_pb'45'jump_1720 v1 v3
du_pb'45'jump_1720 :: Maybe Integer -> T_PBInv_360 -> T_PBInv_360
du_pb'45'jump_1720 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatPtrBounds.pb-ret
d_pb'45'ret_1736 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_PBInv_360 -> T_PBInv_360
d_pb'45'ret_1736 ~v0 v1 ~v2 v3 = du_pb'45'ret_1736 v1 v3
du_pb'45'ret_1736 :: [Integer] -> T_PBInv_360 -> T_PBInv_360
du_pb'45'ret_1736 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatPtrBounds.pb-branch
d_pb'45'branch_1762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_PBInv_360 -> T_PBInv_360
d_pb'45'branch_1762 v0 v1 v2 v3 ~v4 v5
  = du_pb'45'branch_1762 v0 v1 v2 v3 v5
du_pb'45'branch_1762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_PBInv_360 -> T_PBInv_360
du_pb'45'branch_1762 v0 v1 v2 v3 v4
  = if coe v1
      then coe
             du_pb'45'jump_1720
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v0)
                (coe v3) (coe v2))
             (coe v4)
      else coe v4
-- Once.CCC.Machine.FlatPtrBounds.flat-ptr-bounds
d_flat'45'ptr'45'bounds_1788 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  AgdaAny ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506 ->
  T_PBInv_360 -> T_PBInv_360
d_flat'45'ptr'45'bounds_1788 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190
        -> coe
             du_pb'45'write'45'reg_614
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                d_pb'45'regs_382 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192
        -> coe
             du_pb'45'write'45'reg_614
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
             (coe
                d_pb'45'regs_382 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2194
        -> coe
             du_pb'45'write'45'reg_614
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58)
             (coe
                d_pb'45'regs_382 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2196
        -> coe
             du_pb'45'write'45'reg_614
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                d_pb'45'regs_382 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198
        -> coe
             du_pb'45'load'45'resolved_910
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1342
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3)))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200
        -> coe
             du_pb'45'load'45'suc'45'resolved_938
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1342
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3)))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202 v8
        -> coe
             du_pb'45'from'45'slot_1028
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3)))
                   (coe v8)))
             (coe
                du_pb'45'read'45'loc_850 (coe v7)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3)))
                   (coe v8)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204 v8
        -> coe
             du_pb'45'write'45'mem_816 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3)))
                (coe v8))
             (coe
                d_pb'45'regs_382 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206
        -> coe
             du_pb'45'store'45'resolved_966 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1342
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3)))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                d_pb'45'regs_382 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208
        -> coe
             du_pb'45'store'45'suc'45'resolved_998 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1342
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3)))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                d_pb'45'regs_382 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2210 v8
        -> coe
             du_pb'45'write'45'reg_614
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2212 v8
        -> coe
             du_pb'45'restore_1054
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3)))
                   (coe v8)))
             (coe
                du_pb'45'read'45'loc_850 (coe v7)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3)))
                   (coe v8)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2218 v8
        -> coe v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2224
        -> coe v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2226 v8
        -> coe v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2228 v8
        -> coe
             du_pb'45'write'45'mem_816 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3)))
                (coe v8))
             (coe
                d_pb'45'regs_382 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2230 v8
        -> coe
             du_pb'45'from'45'slot_1028
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3)))
                   (coe v8)))
             (coe
                du_pb'45'read'45'loc_850 (coe v7)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3)))
                   (coe v8)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2232 v8
        -> coe v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2238 v8 v9 v10
        -> coe
             du_pb'45'write'45'reg'45'halt_664
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                d_sigop'45'output'45'pb_1190 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2766
                         (coe v0) (coe v1)
                         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
                         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3)))))
                (coe v8) (coe v9) (coe v10)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2242 v8 v9 v10
        -> coe
             du_pb'45'write'45'reg_614
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2244 v8
        -> coe
             du_pb'45'write'45'reg_614
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2246
        -> coe v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2248 v8
        -> coe
             du_pb'45'write'45'reg_614
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252 v8
        -> coe
             d_pb'45'abstract_1242 v0 v1
             (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3)) v4 v5 v6
             v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256 v8
        -> coe
             du_pb'45'reg'45'op_1130
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe v8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258 v8
        -> case coe v8 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176 v9 -> coe v7
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178 v9
               -> coe
                    du_pb'45'jump_1720
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v0)
                       (coe v2) (coe v9))
                    (coe v7)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180 v9
               -> coe
                    du_pb'45'branch_1762 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_94
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3)))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)))
                    (coe v9) (coe v2) (coe v7)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182 v9
               -> coe
                    du_pb'45'branch_1762 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_96
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_108
                          (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))))
                    (coe v9) (coe v2) (coe v7)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2184 v9 v10
               -> coe v7
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2186 v9
               -> coe
                    du_pb'45'ret_1736
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v3))
                    (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
