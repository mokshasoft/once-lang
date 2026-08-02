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
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem'45'aux_812 v2
      v3 v4
-- Once.CCC.Machine.FlatPtrBounds._.writeLoc
d_writeLoc_28 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_writeLoc_28 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_846 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.writeLocToHeap
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
-- Once.CCC.Machine.FlatPtrBounds._.writeLocToStack
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeStackMem'45'aux_786 v4
      v5 v6 v7
-- Once.CCC.Machine.FlatPtrBounds._.exec-load-suc-via-resolved
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
-- Once.CCC.Machine.FlatPtrBounds._.exec-load-via-resolved
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
-- Once.CCC.Machine.FlatPtrBounds._.exec-load-with-value
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
-- Once.CCC.Machine.FlatPtrBounds._.exec-store-suc-via-resolved
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
-- Once.CCC.Machine.FlatPtrBounds._.exec-store-via-resolved
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
-- Once.CCC.Machine.FlatPtrBounds._.exec-abstract
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
-- Once.CCC.Machine.FlatPtrBounds._.exec-load-from-slot-with-value
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
-- Once.CCC.Machine.FlatPtrBounds._.exec-restore-input-with-value
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
-- Once.CCC.Machine.FlatPtrBounds._.exec-sigop-output
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
-- Once.CCC.Machine.FlatPtrBounds._.exec-sigop-output-of
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
-- Once.CCC.Machine.FlatPtrBounds._.pure-sigop-out-aux
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_pure'45'sigop'45'out'45'val_2648
      v1 v2 v3 v4
-- Once.CCC.Machine.FlatPtrBounds._.structured-pure-sigop-output
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
-- Once.CCC.Machine.FlatPtrBounds._.FlatState
d_FlatState_166 a0 = ()
-- Once.CCC.Machine.FlatPtrBounds._.do-branch
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
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_156
-- Once.CCC.Machine.FlatPtrBounds._.flat-exec-instr
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
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.falloc
d_falloc_252 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_falloc_252 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.floc
d_floc_254 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_floc_254 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.fpc
d_fpc_256 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> Integer
d_fpc_256 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_74 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF
d_StoreWF_266 a0 a1 a2 = ()
-- Once.CCC.Machine.FlatPtrBounds._.sv-below
d_sv'45'below_270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_sv'45'below_270 = erased
-- Once.CCC.Machine.FlatPtrBounds._.svm-below
d_svm'45'below_272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_svm'45'below_272 = erased
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF.wf-fresh
d_wf'45'fresh_282 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_456 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wf'45'fresh_282 = erased
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF.wf-heap
d_wf'45'heap_284 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_456 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny
d_wf'45'heap_284 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'heap_486 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF.wf-regs
d_wf'45'regs_286 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
d_wf'45'regs_286 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'regs_482 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF.wf-stack
d_wf'45'stack_288 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_456 ->
  AgdaAny -> Integer -> AgdaAny
d_wf'45'stack_288 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'stack_492
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds.PtrB
d_PtrB_290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_PtrB_290 = erased
-- Once.CCC.Machine.FlatPtrBounds.PtrB?
d_PtrB'63'_298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_PtrB'63'_298 = erased
-- Once.CCC.Machine.FlatPtrBounds.PBInv
d_PBInv_310 a0 a1 a2 = ()
data T_PBInv_310
  = C_mkPtrBounds_344 (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
                       AgdaAny)
                      (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny)
                      (AgdaAny -> Integer -> AgdaAny)
-- Once.CCC.Machine.FlatPtrBounds.PBInv.pb-regs
d_pb'45'regs_332 ::
  T_PBInv_310 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
d_pb'45'regs_332 v0
  = case coe v0 of
      C_mkPtrBounds_344 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.PBInv.pb-heap
d_pb'45'heap_336 ::
  T_PBInv_310 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny
d_pb'45'heap_336 v0
  = case coe v0 of
      C_mkPtrBounds_344 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.PBInv.pb-stack
d_pb'45'stack_342 :: T_PBInv_310 -> AgdaAny -> Integer -> AgdaAny
d_pb'45'stack_342 v0
  = case coe v0 of
      C_mkPtrBounds_344 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.PtrBoundsWF
d_PtrBoundsWF_346 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_PtrBoundsWF_346 = erased
-- Once.CCC.Machine.FlatPtrBounds.ptr-bounds-suc
d_ptr'45'bounds'45'suc_356 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_PBInv_310 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ptr'45'bounds'45'suc_356 ~v0 ~v1 v2 ~v3 v4 ~v5
  = du_ptr'45'bounds'45'suc_356 v2 v4
du_ptr'45'bounds'45'suc_356 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  T_PBInv_310 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ptr'45'bounds'45'suc_356 v0 v1 = coe d_pb'45'regs_332 v1 v0
-- Once.CCC.Machine.FlatPtrBounds.ptr-bounds-cell
d_ptr'45'bounds'45'cell_374 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_PBInv_310 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ptr'45'bounds'45'cell_374 ~v0 ~v1 v2 v3 v4 ~v5
  = du_ptr'45'bounds'45'cell_374 v2 v3 v4
du_ptr'45'bounds'45'cell_374 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_PBInv_310 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ptr'45'bounds'45'cell_374 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50
               (coe v1))))
      (coe du_ptr'45'bounds'45'suc_356 (coe v0) (coe v2))
-- Once.CCC.Machine.FlatPtrBounds.size-with-new
d_size'45'with'45'new_392 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_size'45'with'45'new_392 = erased
-- Once.CCC.Machine.FlatPtrBounds.size-with-old
d_size'45'with'45'old_426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_size'45'with'45'old_426 = erased
-- Once.CCC.Machine.FlatPtrBounds.ptrb-ext
d_ptrb'45'ext_472 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_ptrb'45'ext_472 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_ptrb'45'ext_472 v4 v6
du_ptrb'45'ext_472 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny
du_ptrb'45'ext_472 v0 v1
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
d_pbm'45'ext_520 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_pbm'45'ext_520 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_pbm'45'ext_520 v4 v6
du_pbm'45'ext_520 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny
du_pbm'45'ext_520 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe du_ptrb'45'ext_472 (coe v2) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-halt
d_pb'45'halt_546 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  Bool -> T_PBInv_310 -> T_PBInv_310
d_pb'45'halt_546 ~v0 ~v1 ~v2 ~v3 v4 = du_pb'45'halt_546 v4
du_pb'45'halt_546 :: T_PBInv_310 -> T_PBInv_310
du_pb'45'halt_546 v0 = coe v0
-- Once.CCC.Machine.FlatPtrBounds.pb-write-reg
d_pb'45'write'45'reg_564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_310 -> T_PBInv_310
d_pb'45'write'45'reg_564 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'write'45'reg_564 v3 v5 v6
du_pb'45'write'45'reg_564 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> T_PBInv_310 -> T_PBInv_310
du_pb'45'write'45'reg_564 v0 v1 v2
  = coe
      C_mkPtrBounds_344
      (coe
         (\ v3 ->
            coe
              du_go_584 (coe v1) (coe v2) (coe v3)
              (coe
                 MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.du_readReg'45'write_402
                 (coe v0) (coe v3))))
      (coe d_pb'45'heap_336 (coe v2)) (coe d_pb'45'stack_342 (coe v2))
-- Once.CCC.Machine.FlatPtrBounds._.go
d_go_584 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny ->
  T_PBInv_310 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_go_584 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 = du_go_584 v5 v6 v7 v8
du_go_584 ::
  AgdaAny ->
  T_PBInv_310 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_go_584 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> coe d_pb'45'regs_332 v1 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-write-reg-halt
d_pb'45'write'45'reg'45'halt_614 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Bool -> AgdaAny -> T_PBInv_310 -> T_PBInv_310
d_pb'45'write'45'reg'45'halt_614 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du_pb'45'write'45'reg'45'halt_614 v3 v6 v7
du_pb'45'write'45'reg'45'halt_614 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> T_PBInv_310 -> T_PBInv_310
du_pb'45'write'45'reg'45'halt_614 v0 v1 v2
  = coe du_pb'45'write'45'reg_564 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.FlatPtrBounds.pb-wsm-aux
d_pb'45'wsm'45'aux_648 ::
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
d_pb'45'wsm'45'aux_648 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 v10
                       v11
  = du_pb'45'wsm'45'aux_648 v6 v7 v10 v11
du_pb'45'wsm'45'aux_648 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_pb'45'wsm'45'aux_648 v0 v1 v2 v3
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
d_pb'45'whm'45'aux_686 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_pb'45'whm'45'aux_686 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8
  = du_pb'45'whm'45'aux_686 v4 v7 v8
du_pb'45'whm'45'aux_686 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_pb'45'whm'45'aux_686 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe seq (coe v4) (coe v2)
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-write-stack
d_pb'45'write'45'stack_714 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_310 -> T_PBInv_310
d_pb'45'write'45'stack_714 v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du_pb'45'write'45'stack_714 v0 v3 v4 v6 v7
du_pb'45'write'45'stack_714 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> AgdaAny -> T_PBInv_310 -> T_PBInv_310
du_pb'45'write'45'stack_714 v0 v1 v2 v3 v4
  = coe
      C_mkPtrBounds_344 (coe d_pb'45'regs_332 (coe v4))
      (coe d_pb'45'heap_336 (coe v4))
      (coe
         (\ v5 v6 ->
            coe
              du_pb'45'wsm'45'aux_648
              (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__84 v0 v1 v5)
              (coe
                 MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v2) (coe v6))
              (coe d_pb'45'stack_342 v4 v5 v6) (coe v3)))
-- Once.CCC.Machine.FlatPtrBounds.pb-write-heap
d_pb'45'write'45'heap_742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_310 -> T_PBInv_310
d_pb'45'write'45'heap_742 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'write'45'heap_742 v3 v5 v6
du_pb'45'write'45'heap_742 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> T_PBInv_310 -> T_PBInv_310
du_pb'45'write'45'heap_742 v0 v1 v2
  = coe
      C_mkPtrBounds_344 (coe d_pb'45'regs_332 (coe v2))
      (coe
         (\ v3 ->
            coe
              du_pb'45'whm'45'aux_686
              (coe
                 MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__80 (coe v0)
                 (coe v3))
              (coe d_pb'45'heap_336 v2 v3) (coe v1)))
      (coe d_pb'45'stack_342 (coe v2))
-- Once.CCC.Machine.FlatPtrBounds.pb-write-mem
d_pb'45'write'45'mem_766 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_310 -> T_PBInv_310
d_pb'45'write'45'mem_766 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'write'45'mem_766 v0 v3 v5 v6
du_pb'45'write'45'mem_766 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_PBInv_310 -> T_PBInv_310
du_pb'45'write'45'mem_766 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             du_pb'45'write'45'stack_714 (coe v0) (coe v4) (coe v5) (coe v2)
             (coe v3)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> coe du_pb'45'write'45'heap_742 (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-read-loc
d_pb'45'read'45'loc_800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  T_PBInv_310 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
d_pb'45'read'45'loc_800 ~v0 ~v1 ~v2 v3 v4
  = du_pb'45'read'45'loc_800 v3 v4
du_pb'45'read'45'loc_800 ::
  T_PBInv_310 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
du_pb'45'read'45'loc_800 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe d_pb'45'stack_342 v0 v2 v3
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe d_pb'45'heap_336 v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-load-value
d_pb'45'load'45'value_828 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_310 -> T_PBInv_310
d_pb'45'load'45'value_828 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_pb'45'load'45'value_828 v3 v4 v5 v6
du_pb'45'load'45'value_828 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_310 -> T_PBInv_310
du_pb'45'load'45'value_828 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe du_pb'45'write'45'reg_564 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-load-resolved
d_pb'45'load'45'resolved_860 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_PBInv_310 -> T_PBInv_310
d_pb'45'load'45'resolved_860 ~v0 ~v1 v2 v3 v4 v5
  = du_pb'45'load'45'resolved_860 v2 v3 v4 v5
du_pb'45'load'45'resolved_860 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_PBInv_310 -> T_PBInv_310
du_pb'45'load'45'resolved_860 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_pb'45'load'45'value_828 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v0)
                (coe v4))
             (coe du_pb'45'read'45'loc_800 (coe v3) (coe v4)) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-load-suc-resolved
d_pb'45'load'45'suc'45'resolved_888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_PBInv_310 -> T_PBInv_310
d_pb'45'load'45'suc'45'resolved_888 ~v0 ~v1 v2 v3 v4 v5
  = du_pb'45'load'45'suc'45'resolved_888 v2 v3 v4 v5
du_pb'45'load'45'suc'45'resolved_888 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_PBInv_310 -> T_PBInv_310
du_pb'45'load'45'suc'45'resolved_888 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_pb'45'load'45'value_828 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v0)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v4)))
             (coe
                du_pb'45'read'45'loc_800 (coe v3)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v4)))
             (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-store-resolved
d_pb'45'store'45'resolved_916 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_310 -> T_PBInv_310
d_pb'45'store'45'resolved_916 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'store'45'resolved_916 v0 v3 v5 v6
du_pb'45'store'45'resolved_916 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_PBInv_310 -> T_PBInv_310
du_pb'45'store'45'resolved_916 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_pb'45'write'45'mem_766 (coe v0) (coe v4) (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-store-suc-resolved
d_pb'45'store'45'suc'45'resolved_948 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_310 -> T_PBInv_310
d_pb'45'store'45'suc'45'resolved_948 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'store'45'suc'45'resolved_948 v0 v3 v5 v6
du_pb'45'store'45'suc'45'resolved_948 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_PBInv_310 -> T_PBInv_310
du_pb'45'store'45'suc'45'resolved_948 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_pb'45'write'45'mem_766 (coe v0)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v4))
             (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-from-slot
d_pb'45'from'45'slot_978 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_310 -> T_PBInv_310
d_pb'45'from'45'slot_978 ~v0 ~v1 ~v2 v3 v4 v5
  = du_pb'45'from'45'slot_978 v3 v4 v5
du_pb'45'from'45'slot_978 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_310 -> T_PBInv_310
du_pb'45'from'45'slot_978 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_pb'45'write'45'reg_564
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v1)
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-restore
d_pb'45'restore_1004 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_310 -> T_PBInv_310
d_pb'45'restore_1004 ~v0 ~v1 ~v2 v3 v4 v5
  = du_pb'45'restore_1004 v3 v4 v5
du_pb'45'restore_1004 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_PBInv_310 -> T_PBInv_310
du_pb'45'restore_1004 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_pb'45'write'45'reg_564
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v1)
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-pred
d_pb'45'pred_1028 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
d_pb'45'pred_1028 ~v0 ~v1 v2 = du_pb'45'pred_1028 v2
du_pb'45'pred_1028 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
du_pb'45'pred_1028 v0
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
d_pb'45'succ_1054 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
d_pb'45'succ_1054 ~v0 ~v1 v2 = du_pb'45'succ_1054 v2
du_pb'45'succ_1054 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
du_pb'45'succ_1054 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatPtrBounds.pb-reg-op
d_pb'45'reg'45'op_1080 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_506 ->
  T_PBInv_310 -> T_PBInv_310
d_pb'45'reg'45'op_1080 ~v0 ~v1 v2 v3 v4
  = du_pb'45'reg'45'op_1080 v2 v3 v4
du_pb'45'reg'45'op_1080 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_506 ->
  T_PBInv_310 -> T_PBInv_310
du_pb'45'reg'45'op_1080 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_508
        -> coe
             du_pb'45'write'45'reg_564
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_510
        -> coe
             du_pb'45'write'45'reg_564
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_512
        -> coe
             du_pb'45'write'45'reg_564
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe
                du_pb'45'pred_1028
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v0))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)))
             (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_514
        -> coe
             du_pb'45'write'45'reg_564
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe
                d_pb'45'regs_332 v2
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64))
             (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_516
        -> coe
             du_pb'45'write'45'reg_564
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_518
        -> coe
             du_pb'45'write'45'reg_564
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64)
             (coe
                du_pb'45'succ_1054
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v0))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64)))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.structured-pure-sigop-inbounds
d_structured'45'pure'45'sigop'45'inbounds_1128
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.FlatPtrBounds.structured-pure-sigop-inbounds"
-- Once.CCC.Machine.FlatPtrBounds.sigop-output-pb
d_sigop'45'output'45'pb_1140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 -> AgdaAny
d_sigop'45'output'45'pb_1140 v0 v1 v2 v3 v4 v5
  = coe
      d_go_1182 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_212 (coe v4))
-- Once.CCC.Machine.FlatPtrBounds._.pov
d_pov_1160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 -> Maybe AgdaAny -> AgdaAny
d_pov_1160 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_pov_1160 v7
du_pov_1160 :: Maybe AgdaAny -> AgdaAny
du_pov_1160 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatPtrBounds._.aux
d_aux_1172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
d_aux_1172 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> coe
                    du_pov_1160
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2606 (coe v2)
                       (coe v9) (coe v5))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    du_pov_1160
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
             d_structured'45'pure'45'sigop'45'inbounds_1128 v0 v1 v2 v3 v4 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds._.go
d_go_1182 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 -> AgdaAny
d_go_1182 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_124
        -> coe
             d_aux_1172 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
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
-- Once.CCC.Machine.FlatPtrBounds.pb-abstract
d_pb'45'abstract_1192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  AgdaAny ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_456 ->
  T_PBInv_310 -> T_PBInv_310
d_pb'45'abstract_1192 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'write'45'reg_564
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe
                     d_pb'45'regs_332 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'write'45'reg_564
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
                  (coe
                     d_pb'45'regs_332 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2244
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'write'45'reg_564
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58)
                  (coe
                     d_pb'45'regs_332 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2246
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'write'45'reg_564
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe
                     d_pb'45'regs_332 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2248
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'load'45'resolved_860 (coe v2)
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1396
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2250
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'load'45'suc'45'resolved_888 (coe v2)
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1396
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2252 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'from'45'slot_978
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v3)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                           (coe v4))
                        (coe v2)))
                  (coe
                     du_pb'45'read'45'loc_800 (coe v8)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                           (coe v4))
                        (coe v2)))
                  (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2254 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'write'45'mem_766 (coe v0)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                        (coe v4))
                     (coe v2))
                  (coe
                     d_pb'45'regs_332 v8
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2256
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'store'45'resolved_916 (coe v0)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1396
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                  (coe
                     d_pb'45'regs_332 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2258
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'store'45'suc'45'resolved_948 (coe v0)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1396
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                  (coe
                     d_pb'45'regs_332 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2260 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'write'45'reg_564
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2262 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'restore_1004
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v3)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                           (coe v4))
                        (coe v2)))
                  (coe
                     du_pb'45'read'45'loc_800 (coe v8)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                           (coe v4))
                        (coe v2)))
                  (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2264 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2266 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2268 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2270 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2272
        -> coe (\ v2 v3 v4 v5 v6 v7 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2274
        -> coe (\ v2 v3 v4 v5 v6 v7 -> v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2276 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2278 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'write'45'mem_766 (coe v0)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                        (coe v4))
                     (coe v2))
                  (coe
                     d_pb'45'regs_332 v8
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
                  (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2280 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'from'45'slot_978
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v3)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                           (coe v4))
                        (coe v2)))
                  (coe
                     du_pb'45'read'45'loc_800 (coe v8)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                           (coe v4))
                        (coe v2)))
                  (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2282 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2288 v2 v3 v4
        -> coe
             (\ v5 v6 v7 v8 v9 v10 ->
                coe
                  du_pb'45'write'45'reg'45'halt_614
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe
                     d_sigop'45'output'45'pb_1140 (coe v0)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_712
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2816
                              (coe v0) (coe v1) (coe v5) (coe v6))))
                     (coe v2) (coe v3) (coe v4) (coe v5))
                  (coe v10))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2292 v2 v3 v4
        -> coe
             (\ v5 v6 v7 v8 v9 v10 ->
                coe
                  du_pb'45'write'45'reg_564
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v10))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2294 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'write'45'reg_564
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2296
        -> coe (\ v2 v3 v4 v5 v6 v7 -> v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2298 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'write'45'reg_564
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2300 v2 v3
        -> coe (\ v4 v5 v6 v7 v8 v9 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2302 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  C_mkPtrBounds_344
                  (coe
                     (\ v9 ->
                        coe
                          du_go_1612 (coe v2) (coe v3) (coe v6) (coe v8) (coe v9)
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.du_readReg'45'write_402
                             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v9))))
                  (coe
                     (\ v9 ->
                        coe
                          du_pbm'45'ext_520
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_556 v3 v9)
                          (coe d_pb'45'heap_336 v8 v9)))
                  (coe
                     (\ v9 v10 ->
                        coe
                          du_pbm'45'ext_520
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_554 v3 v9 v10)
                          (coe d_pb'45'stack_342 v8 v9 v10))))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2304 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2306 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe du_pb'45'reg'45'op_1080 (coe v3) (coe v2) (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2308 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2310 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds._.st
d_st_1600 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_456 ->
  T_PBInv_310 -> Integer
d_st_1600 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 = du_st_1600 v3
du_st_1600 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 -> Integer
du_st_1600 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.bs
d_bs_1602 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_456 ->
  T_PBInv_310 -> Integer -> Integer
d_bs_1602 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 = du_bs_1602 v3
du_bs_1602 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer -> Integer
du_bs_1602 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_712 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.fresh
d_fresh_1604 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_456 ->
  T_PBInv_310 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fresh_1604 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 = du_fresh_1604 v3
du_fresh_1604 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_fresh_1604 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
               (coe du_st_1600 (coe v0)))
            (coe (0 :: Integer))))
-- Once.CCC.Machine.FlatPtrBounds._.fresh-ok
d_fresh'45'ok_1606 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_456 ->
  T_PBInv_310 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fresh'45'ok_1606 ~v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7
  = du_fresh'45'ok_1606 v1 v5
du_fresh'45'ok_1606 ::
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fresh'45'ok_1606 v0 v1 = coe v1 v0 erased
-- Once.CCC.Machine.FlatPtrBounds._.go
d_go_1612 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_456 ->
  T_PBInv_310 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_go_1612 ~v0 v1 v2 ~v3 ~v4 v5 ~v6 v7 v8 v9
  = du_go_1612 v1 v2 v5 v7 v8 v9
du_go_1612 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  T_PBInv_310 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_go_1612 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
        -> coe du_fresh'45'ok_1606 (coe v0) (coe v2)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> coe
             du_ptrb'45'ext_472
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v1))
                (coe v4))
             (coe d_pb'45'regs_332 v3 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-jump
d_pb'45'jump_1670 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_PBInv_310 -> T_PBInv_310
d_pb'45'jump_1670 ~v0 v1 ~v2 v3 = du_pb'45'jump_1670 v1 v3
du_pb'45'jump_1670 :: Maybe Integer -> T_PBInv_310 -> T_PBInv_310
du_pb'45'jump_1670 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatPtrBounds.pb-branch
d_pb'45'branch_1690 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_PBInv_310 -> T_PBInv_310
d_pb'45'branch_1690 v0 v1 v2 v3 ~v4 v5
  = du_pb'45'branch_1690 v0 v1 v2 v3 v5
du_pb'45'branch_1690 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_PBInv_310 -> T_PBInv_310
du_pb'45'branch_1690 v0 v1 v2 v3 v4
  = if coe v1
      then coe
             du_pb'45'jump_1670
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_142 (coe v0)
                (coe v3) (coe v2))
             (coe v4)
      else coe v4
-- Once.CCC.Machine.FlatPtrBounds.flat-ptr-bounds
d_flat'45'ptr'45'bounds_1716 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  AgdaAny ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_456 ->
  T_PBInv_310 -> T_PBInv_310
d_flat'45'ptr'45'bounds_1716 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240
        -> coe
             du_pb'45'write'45'reg_564
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                d_pb'45'regs_332 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242
        -> coe
             du_pb'45'write'45'reg_564
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
             (coe
                d_pb'45'regs_332 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2244
        -> coe
             du_pb'45'write'45'reg_564
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58)
             (coe
                d_pb'45'regs_332 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2246
        -> coe
             du_pb'45'write'45'reg_564
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                d_pb'45'regs_332 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2248
        -> coe
             du_pb'45'load'45'resolved_860
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1396
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3)))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2250
        -> coe
             du_pb'45'load'45'suc'45'resolved_888
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1396
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3)))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2252 v8
        -> coe
             du_pb'45'from'45'slot_978
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3)))
                   (coe v8)))
             (coe
                du_pb'45'read'45'loc_800 (coe v7)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3)))
                   (coe v8)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2254 v8
        -> coe
             du_pb'45'write'45'mem_766 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3)))
                (coe v8))
             (coe
                d_pb'45'regs_332 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2256
        -> coe
             du_pb'45'store'45'resolved_916 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1396
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3)))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                d_pb'45'regs_332 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2258
        -> coe
             du_pb'45'store'45'suc'45'resolved_948 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1396
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3)))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                d_pb'45'regs_332 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2260 v8
        -> coe
             du_pb'45'write'45'reg_564
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2262 v8
        -> coe
             du_pb'45'restore_1004
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3)))
                   (coe v8)))
             (coe
                du_pb'45'read'45'loc_800 (coe v7)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3)))
                   (coe v8)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2268 v8
        -> coe v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2274
        -> coe v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2276 v8
        -> coe v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2278 v8
        -> coe
             du_pb'45'write'45'mem_766 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3)))
                (coe v8))
             (coe
                d_pb'45'regs_332 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2280 v8
        -> coe
             du_pb'45'from'45'slot_978
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3)))
                   (coe v8)))
             (coe
                du_pb'45'read'45'loc_800 (coe v7)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3)))
                   (coe v8)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2282 v8
        -> coe v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2288 v8 v9 v10
        -> coe
             du_pb'45'write'45'reg'45'halt_614
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                d_sigop'45'output'45'pb_1140 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_712
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2816
                         (coe v0) (coe v1)
                         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
                         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3)))))
                (coe v8) (coe v9) (coe v10)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2292 v8 v9 v10
        -> coe
             du_pb'45'write'45'reg_564
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2294 v8
        -> coe
             du_pb'45'write'45'reg_564
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2296
        -> coe v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2298 v8
        -> coe
             du_pb'45'write'45'reg_564
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2302 v8
        -> coe
             d_pb'45'abstract_1192 v0 v1
             (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3)) v4 v5 v6
             v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2306 v8
        -> coe
             du_pb'45'reg'45'op_1080
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe v8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2308 v8
        -> case coe v8 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2230 v9 -> coe v7
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2232 v9
               -> coe
                    du_pb'45'jump_1670
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_142 (coe v0)
                       (coe v2) (coe v9))
                    (coe v7)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2234 v9
               -> coe
                    du_pb'45'branch_1690 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_78
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552
                             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3)))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)))
                    (coe v9) (coe v2) (coe v7)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2236 v9
               -> coe
                    du_pb'45'branch_1690 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_80
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_92
                          (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))))
                    (coe v9) (coe v2) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
