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

module MAlonzo.Code.Once.CCC.Machine.FlatStackPtr where

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
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Machine.FlatStackPtr._.readLoc
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
-- Once.CCC.Machine.FlatStackPtr._.writeHeapMem-aux
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
-- Once.CCC.Machine.FlatStackPtr._.writeLoc
d_writeLoc_28 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_writeLoc_28 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_792 (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.writeLocToHeap
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
-- Once.CCC.Machine.FlatStackPtr._.writeLocToStack
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
-- Once.CCC.Machine.FlatStackPtr._.writeStackMem-aux
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
-- Once.CCC.Machine.FlatStackPtr._.exec-load-suc-via-resolved
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
-- Once.CCC.Machine.FlatStackPtr._.exec-load-via-resolved
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
-- Once.CCC.Machine.FlatStackPtr._.exec-load-with-value
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
-- Once.CCC.Machine.FlatStackPtr._.exec-store-suc-via-resolved
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
-- Once.CCC.Machine.FlatStackPtr._.exec-store-via-resolved
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
-- Once.CCC.Machine.FlatStackPtr._.exec-abstract
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
-- Once.CCC.Machine.FlatStackPtr._.exec-load-from-slot-with-value
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
-- Once.CCC.Machine.FlatStackPtr._.exec-restore-input-with-value
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
-- Once.CCC.Machine.FlatStackPtr._.exec-sigop-output
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
-- Once.CCC.Machine.FlatStackPtr._.exec-sigop-output-of
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
-- Once.CCC.Machine.FlatStackPtr._.pure-sigop-out-aux
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
-- Once.CCC.Machine.FlatStackPtr._.pure-sigop-out-val
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
-- Once.CCC.Machine.FlatStackPtr._.structured-pure-sigop-output
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
-- Once.CCC.Machine.FlatStackPtr._.FlatState
d_FlatState_166 a0 = ()
-- Once.CCC.Machine.FlatStackPtr._.do-branch
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
-- Once.CCC.Machine.FlatStackPtr._.do-jump
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
-- Once.CCC.Machine.FlatStackPtr._.do-ret
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
-- Once.CCC.Machine.FlatStackPtr._.flat-exec-instr
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
-- Once.CCC.Machine.FlatStackPtr._.FlatState.falloc
d_falloc_298 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_falloc_298 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.FlatState.fclosure
d_fclosure_300 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fclosure_300 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_82 (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.FlatState.floc
d_floc_302 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_floc_302 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.FlatState.fpc
d_fpc_304 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> Integer
d_fpc_304 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.FlatState.fret
d_fret_306 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> [Integer]
d_fret_306 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v0)
-- Once.CCC.Machine.FlatStackPtr.StackPtrOK
d_StackPtrOK_308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_StackPtrOK_308 = erased
-- Once.CCC.Machine.FlatStackPtr.StackPtrOK?
d_StackPtrOK'63'_314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_StackPtrOK'63'_314 = erased
-- Once.CCC.Machine.FlatStackPtr.SPInv
d_SPInv_320 a0 a1 = ()
data T_SPInv_320
  = C_mkStackPtrWF_352 (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
                        AgdaAny)
                       (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny)
                       (AgdaAny -> Integer -> AgdaAny)
-- Once.CCC.Machine.FlatStackPtr.SPInv.sp-regs
d_sp'45'regs_340 ::
  T_SPInv_320 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
d_sp'45'regs_340 v0
  = case coe v0 of
      C_mkStackPtrWF_352 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.SPInv.sp-heap
d_sp'45'heap_344 ::
  T_SPInv_320 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny
d_sp'45'heap_344 v0
  = case coe v0 of
      C_mkStackPtrWF_352 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.SPInv.sp-stack
d_sp'45'stack_350 :: T_SPInv_320 -> AgdaAny -> Integer -> AgdaAny
d_sp'45'stack_350 v0
  = case coe v0 of
      C_mkStackPtrWF_352 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.StackPtrWF
d_StackPtrWF_354 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_StackPtrWF_354 = erased
-- Once.CCC.Machine.FlatStackPtr.stack-ptr-frame
d_stack'45'ptr'45'frame_366 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  Integer ->
  T_SPInv_320 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'ptr'45'frame_366 = erased
-- Once.CCC.Machine.FlatStackPtr.stack-ptr-suc-live
d_stack'45'ptr'45'suc'45'live_388 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  Integer ->
  T_SPInv_320 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_stack'45'ptr'45'suc'45'live_388 = erased
-- Once.CCC.Machine.FlatStackPtr.stack-ptr-live
d_stack'45'ptr'45'live_410 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  Integer ->
  T_SPInv_320 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_stack'45'ptr'45'live_410 = erased
-- Once.CCC.Machine.FlatStackPtr.readReg-write
d_readReg'45'write_432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_126 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_readReg'45'write_432 ~v0 ~v1 v2 v3 ~v4
  = du_readReg'45'write_432 v2 v3
du_readReg'45'write_432 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_readReg'45'write_432 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-halt
d_sp'45'halt_540 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Bool -> T_SPInv_320 -> T_SPInv_320
d_sp'45'halt_540 ~v0 ~v1 ~v2 ~v3 v4 = du_sp'45'halt_540 v4
du_sp'45'halt_540 :: T_SPInv_320 -> T_SPInv_320
du_sp'45'halt_540 v0 = coe v0
-- Once.CCC.Machine.FlatStackPtr.sp-write-reg
d_sp'45'write'45'reg_558 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_320 -> T_SPInv_320
d_sp'45'write'45'reg_558 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_sp'45'write'45'reg_558 v3 v5 v6
du_sp'45'write'45'reg_558 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> T_SPInv_320 -> T_SPInv_320
du_sp'45'write'45'reg_558 v0 v1 v2
  = coe
      C_mkStackPtrWF_352
      (coe
         (\ v3 ->
            coe
              du_go_578 (coe v1) (coe v2) (coe v3)
              (coe du_readReg'45'write_432 (coe v0) (coe v3))))
      (coe d_sp'45'heap_344 (coe v2)) (coe d_sp'45'stack_350 (coe v2))
-- Once.CCC.Machine.FlatStackPtr._.go
d_go_578 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny ->
  T_SPInv_320 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_go_578 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 = du_go_578 v5 v6 v7 v8
du_go_578 ::
  AgdaAny ->
  T_SPInv_320 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_go_578 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> coe d_sp'45'regs_340 v1 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-write-reg-halt
d_sp'45'write'45'reg'45'halt_614 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Bool -> AgdaAny -> T_SPInv_320 -> T_SPInv_320
d_sp'45'write'45'reg'45'halt_614 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du_sp'45'write'45'reg'45'halt_614 v3 v6 v7
du_sp'45'write'45'reg'45'halt_614 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> T_SPInv_320 -> T_SPInv_320
du_sp'45'write'45'reg'45'halt_614 v0 v1 v2
  = coe du_sp'45'write'45'reg_558 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.FlatStackPtr.sp-wsm-aux
d_sp'45'wsm'45'aux_646 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_sp'45'wsm'45'aux_646 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 v9 v10
  = du_sp'45'wsm'45'aux_646 v5 v6 v9 v10
du_sp'45'wsm'45'aux_646 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_sp'45'wsm'45'aux_646 v0 v1 v2 v3
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
-- Once.CCC.Machine.FlatStackPtr.sp-whm-aux
d_sp'45'whm'45'aux_682 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_sp'45'whm'45'aux_682 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du_sp'45'whm'45'aux_682 v3 v6 v7
du_sp'45'whm'45'aux_682 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_sp'45'whm'45'aux_682 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe seq (coe v4) (coe v2)
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-write-stack
d_sp'45'write'45'stack_710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_320 -> T_SPInv_320
d_sp'45'write'45'stack_710 v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du_sp'45'write'45'stack_710 v0 v3 v4 v6 v7
du_sp'45'write'45'stack_710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> AgdaAny -> T_SPInv_320 -> T_SPInv_320
du_sp'45'write'45'stack_710 v0 v1 v2 v3 v4
  = coe
      C_mkStackPtrWF_352 (coe d_sp'45'regs_340 (coe v4))
      (coe d_sp'45'heap_344 (coe v4))
      (coe
         (\ v5 v6 ->
            coe
              du_sp'45'wsm'45'aux_646
              (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__84 v0 v1 v5)
              (coe
                 MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v2) (coe v6))
              (coe d_sp'45'stack_350 v4 v5 v6) (coe v3)))
-- Once.CCC.Machine.FlatStackPtr.sp-write-heap
d_sp'45'write'45'heap_738 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_320 -> T_SPInv_320
d_sp'45'write'45'heap_738 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_sp'45'write'45'heap_738 v3 v5 v6
du_sp'45'write'45'heap_738 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> T_SPInv_320 -> T_SPInv_320
du_sp'45'write'45'heap_738 v0 v1 v2
  = coe
      C_mkStackPtrWF_352 (coe d_sp'45'regs_340 (coe v2))
      (coe
         (\ v3 ->
            coe
              du_sp'45'whm'45'aux_682
              (coe
                 MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__80 (coe v0)
                 (coe v3))
              (coe d_sp'45'heap_344 v2 v3) (coe v1)))
      (coe d_sp'45'stack_350 (coe v2))
-- Once.CCC.Machine.FlatStackPtr.writeLoc-dyn
d_writeLoc'45'dyn_760 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'dyn_760 = erased
-- Once.CCC.Machine.FlatStackPtr.sp-write-mem
d_sp'45'write'45'mem_804 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_320 -> T_SPInv_320
d_sp'45'write'45'mem_804 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_sp'45'write'45'mem_804 v0 v3 v5 v6
du_sp'45'write'45'mem_804 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_SPInv_320 -> T_SPInv_320
du_sp'45'write'45'mem_804 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             du_sp'45'write'45'stack_710 (coe v0) (coe v4) (coe v5) (coe v2)
             (coe v3)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> coe du_sp'45'write'45'heap_738 (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-read-loc
d_sp'45'read'45'loc_838 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_SPInv_320 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
d_sp'45'read'45'loc_838 ~v0 ~v1 ~v2 v3 v4
  = du_sp'45'read'45'loc_838 v3 v4
du_sp'45'read'45'loc_838 ::
  T_SPInv_320 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
du_sp'45'read'45'loc_838 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe d_sp'45'stack_350 v0 v2 v3
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe d_sp'45'heap_344 v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-load-value
d_sp'45'load'45'value_866 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_320 -> T_SPInv_320
d_sp'45'load'45'value_866 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_sp'45'load'45'value_866 v3 v4 v5 v6
du_sp'45'load'45'value_866 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_320 -> T_SPInv_320
du_sp'45'load'45'value_866 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe du_sp'45'write'45'reg_558 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-load-resolved
d_sp'45'load'45'resolved_898 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_SPInv_320 -> T_SPInv_320
d_sp'45'load'45'resolved_898 ~v0 ~v1 v2 v3 v4 v5
  = du_sp'45'load'45'resolved_898 v2 v3 v4 v5
du_sp'45'load'45'resolved_898 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_SPInv_320 -> T_SPInv_320
du_sp'45'load'45'resolved_898 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_sp'45'load'45'value_866 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v0)
                (coe v4))
             (coe du_sp'45'read'45'loc_838 (coe v3) (coe v4)) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-load-suc-resolved
d_sp'45'load'45'suc'45'resolved_926 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_SPInv_320 -> T_SPInv_320
d_sp'45'load'45'suc'45'resolved_926 ~v0 ~v1 v2 v3 v4 v5
  = du_sp'45'load'45'suc'45'resolved_926 v2 v3 v4 v5
du_sp'45'load'45'suc'45'resolved_926 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_SPInv_320 -> T_SPInv_320
du_sp'45'load'45'suc'45'resolved_926 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_sp'45'load'45'value_866 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v0)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v4)))
             (coe
                du_sp'45'read'45'loc_838 (coe v3)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v4)))
             (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-store-resolved
d_sp'45'store'45'resolved_954 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_320 -> T_SPInv_320
d_sp'45'store'45'resolved_954 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_sp'45'store'45'resolved_954 v0 v3 v5 v6
du_sp'45'store'45'resolved_954 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_SPInv_320 -> T_SPInv_320
du_sp'45'store'45'resolved_954 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_sp'45'write'45'mem_804 (coe v0) (coe v4) (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-store-suc-resolved
d_sp'45'store'45'suc'45'resolved_986 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_320 -> T_SPInv_320
d_sp'45'store'45'suc'45'resolved_986 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_sp'45'store'45'suc'45'resolved_986 v0 v3 v5 v6
du_sp'45'store'45'suc'45'resolved_986 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_SPInv_320 -> T_SPInv_320
du_sp'45'store'45'suc'45'resolved_986 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_sp'45'write'45'mem_804 (coe v0)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v4))
             (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-from-slot
d_sp'45'from'45'slot_1016 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_320 -> T_SPInv_320
d_sp'45'from'45'slot_1016 ~v0 ~v1 ~v2 v3 v4 v5
  = du_sp'45'from'45'slot_1016 v3 v4 v5
du_sp'45'from'45'slot_1016 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_320 -> T_SPInv_320
du_sp'45'from'45'slot_1016 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_sp'45'write'45'reg_558
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v1)
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-restore
d_sp'45'restore_1042 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_320 -> T_SPInv_320
d_sp'45'restore_1042 ~v0 ~v1 ~v2 v3 v4 v5
  = du_sp'45'restore_1042 v3 v4 v5
du_sp'45'restore_1042 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_320 -> T_SPInv_320
du_sp'45'restore_1042 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_sp'45'write'45'reg_558
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v1)
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-pred
d_sp'45'pred_1064 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
d_sp'45'pred_1064 ~v0 v1 = du_sp'45'pred_1064 v1
du_sp'45'pred_1064 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
du_sp'45'pred_1064 v0
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
-- Once.CCC.Machine.FlatStackPtr.sp-succ
d_sp'45'succ_1078 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
d_sp'45'succ_1078 ~v0 v1 = du_sp'45'succ_1078 v1
du_sp'45'succ_1078 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
du_sp'45'succ_1078 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatStackPtr.sp-reg-op
d_sp'45'reg'45'op_1096 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_448 ->
  T_SPInv_320 -> T_SPInv_320
d_sp'45'reg'45'op_1096 ~v0 ~v1 v2 v3 v4
  = du_sp'45'reg'45'op_1096 v2 v3 v4
du_sp'45'reg'45'op_1096 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_448 ->
  T_SPInv_320 -> T_SPInv_320
du_sp'45'reg'45'op_1096 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_450
        -> coe
             du_sp'45'write'45'reg_558
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_452
        -> coe
             du_sp'45'write'45'reg_558
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_454
        -> coe
             du_sp'45'write'45'reg_558
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe
                du_sp'45'pred_1064
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v0))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)))
             (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_456
        -> coe
             du_sp'45'write'45'reg_558
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe
                d_sp'45'regs_340 v2
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64))
             (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_458
        -> coe
             du_sp'45'write'45'reg_558
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_460
        -> coe
             du_sp'45'write'45'reg_558
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64)
             (coe
                du_sp'45'succ_1078
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v0))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64)))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.structured-pure-sigop-no-stack
d_structured'45'pure'45'sigop'45'no'45'stack_1142
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.FlatStackPtr.structured-pure-sigop-no-stack"
-- Once.CCC.Machine.FlatStackPtr.sigop-output-ok
d_sigop'45'output'45'ok_1152 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 -> AgdaAny
d_sigop'45'output'45'ok_1152 v0 v1 v2 v3 v4
  = coe
      d_go_1192 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_212 (coe v3))
-- Once.CCC.Machine.FlatStackPtr._.pov
d_pov_1170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 -> Maybe AgdaAny -> AgdaAny
d_pov_1170 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_pov_1170 v6
du_pov_1170 :: Maybe AgdaAny -> AgdaAny
du_pov_1170 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatStackPtr._.aux
d_aux_1182 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
d_aux_1182 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
               -> coe
                    du_pov_1170
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2556 (coe v1)
                       (coe v8) (coe v4))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    du_pov_1170
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg'45'typed_2550
                       (coe v1)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v4))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             d_structured'45'pure'45'sigop'45'no'45'stack_1142 v0 v1 v2 v3 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr._.go
d_go_1192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 -> AgdaAny
d_go_1192 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_124
        -> coe
             d_aux_1182 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_204 (coe v2))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1342
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v4))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
      MAlonzo.Code.Once.SigOp.Info.C_Emits_126
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.SigOp.Info.C_Halts_128
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-abstract
d_sp'45'abstract_1200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny -> T_SPInv_320 -> T_SPInv_320
d_sp'45'abstract_1200 v0 v1 v2 v3 ~v4 v5
  = du_sp'45'abstract_1200 v0 v1 v2 v3 v5
du_sp'45'abstract_1200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_SPInv_320 -> T_SPInv_320
du_sp'45'abstract_1200 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190
        -> coe
             du_sp'45'write'45'reg_558
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                d_sp'45'regs_340 v4
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192
        -> coe
             du_sp'45'write'45'reg_558
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
             (coe
                d_sp'45'regs_340 v4
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2194
        -> coe
             du_sp'45'write'45'reg_558
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58)
             (coe
                d_sp'45'regs_340 v4
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2196
        -> coe
             du_sp'45'write'45'reg_558
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                d_sp'45'regs_340 v4
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198
        -> coe
             du_sp'45'load'45'resolved_898 (coe v2)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1342
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200
        -> coe
             du_sp'45'load'45'suc'45'resolved_926 (coe v2)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1342
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202 v5
        -> coe
             du_sp'45'from'45'slot_1016
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe v3))
                   (coe v5)))
             (coe
                du_sp'45'read'45'loc_838 (coe v4)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe v3))
                   (coe v5)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204 v5
        -> coe
             du_sp'45'write'45'mem_804 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                   (coe v3))
                (coe v5))
             (coe
                d_sp'45'regs_340 v4
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206
        -> coe
             du_sp'45'store'45'resolved_954 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1342
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                d_sp'45'regs_340 v4
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208
        -> coe
             du_sp'45'store'45'suc'45'resolved_986 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1342
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                d_sp'45'regs_340 v4
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2212 v5
        -> coe
             du_sp'45'restore_1042
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe v3))
                   (coe v5)))
             (coe
                du_sp'45'read'45'loc_838 (coe v4)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe v3))
                   (coe v5)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2218 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2224
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2226 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2228 v5
        -> coe
             du_sp'45'write'45'mem_804 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                   (coe v3))
                (coe v5))
             (coe
                d_sp'45'regs_340 v4
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2230 v5
        -> coe
             du_sp'45'from'45'slot_1016
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe v3))
                   (coe v5)))
             (coe
                du_sp'45'read'45'loc_838 (coe v4)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                      (coe v3))
                   (coe v5)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2232 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2238 v5 v6 v7
        -> coe
             du_sp'45'write'45'reg'45'halt_614
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                d_sigop'45'output'45'ok_1152 (coe v0) (coe v5) (coe v6) (coe v7)
                (coe v2))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2242 v5 v6 v7
        -> coe
             du_sp'45'write'45'reg_558
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2244 v5
        -> coe
             du_sp'45'write'45'reg_558
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2246
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2248 v5
        -> coe
             du_sp'45'write'45'reg_558
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252 v5
        -> coe
             du_sp'45'write'45'reg_558
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256 v5
        -> coe du_sp'45'reg'45'op_1096 (coe v2) (coe v5) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258 v5
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-jump
d_sp'45'jump_1502 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_SPInv_320 -> T_SPInv_320
d_sp'45'jump_1502 ~v0 v1 ~v2 v3 = du_sp'45'jump_1502 v1 v3
du_sp'45'jump_1502 :: Maybe Integer -> T_SPInv_320 -> T_SPInv_320
du_sp'45'jump_1502 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatStackPtr.sp-branch
d_sp'45'branch_1522 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_SPInv_320 -> T_SPInv_320
d_sp'45'branch_1522 v0 v1 v2 v3 ~v4 v5
  = du_sp'45'branch_1522 v0 v1 v2 v3 v5
du_sp'45'branch_1522 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_SPInv_320 -> T_SPInv_320
du_sp'45'branch_1522 v0 v1 v2 v3 v4
  = if coe v1
      then coe
             du_sp'45'jump_1502
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v0)
                (coe v3) (coe v2))
             (coe v4)
      else coe v4
-- Once.CCC.Machine.FlatStackPtr.sp-ret
d_sp'45'ret_1544 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_SPInv_320 -> T_SPInv_320
d_sp'45'ret_1544 ~v0 v1 ~v2 v3 = du_sp'45'ret_1544 v1 v3
du_sp'45'ret_1544 :: [Integer] -> T_SPInv_320 -> T_SPInv_320
du_sp'45'ret_1544 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatStackPtr.flat-stack-ptr
d_flat'45'stack'45'ptr_1564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  AgdaAny -> T_SPInv_320 -> T_SPInv_320
d_flat'45'stack'45'ptr_1564 v0 v1 v2 v3 ~v4 v5
  = du_flat'45'stack'45'ptr_1564 v0 v1 v2 v3 v5
du_flat'45'stack'45'ptr_1564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_SPInv_320 -> T_SPInv_320
du_flat'45'stack'45'ptr_1564 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2194
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2196
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202 v5
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204 v5
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2212 v5
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2218 v5
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2224
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2226 v5
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2228 v5
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2230 v5
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2232 v5
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2238 v5 v6 v7
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2242 v5 v6 v7
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2244 v5
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2246
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2248 v5
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252 v5
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256 v5
        -> coe
             du_sp'45'abstract_1200 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258 v5
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176 v6 -> coe v4
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178 v6
               -> coe
                    du_sp'45'jump_1502
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v0)
                       (coe v2) (coe v6))
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180 v6
               -> coe
                    du_sp'45'branch_1522 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_94
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3)))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)))
                    (coe v6) (coe v2) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182 v6
               -> coe
                    du_sp'45'branch_1522 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_96
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_108
                          (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))))
                    (coe v6) (coe v2) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2184 v6 v7
               -> coe v4
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2186 v6
               -> coe
                    du_sp'45'ret_1544
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v3))
                    (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
