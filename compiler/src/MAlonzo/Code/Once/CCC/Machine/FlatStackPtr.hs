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
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem'45'aux_812 v2
      v3 v4
-- Once.CCC.Machine.FlatStackPtr._.writeLoc
d_writeLoc_28 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_writeLoc_28 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_846 (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.writeLocToHeap
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
-- Once.CCC.Machine.FlatStackPtr._.writeLocToStack
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeStackMem'45'aux_786 v4
      v5 v6 v7
-- Once.CCC.Machine.FlatStackPtr._.exec-load-suc-via-resolved
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
-- Once.CCC.Machine.FlatStackPtr._.exec-load-via-resolved
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
-- Once.CCC.Machine.FlatStackPtr._.exec-load-with-value
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
-- Once.CCC.Machine.FlatStackPtr._.exec-store-suc-via-resolved
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
-- Once.CCC.Machine.FlatStackPtr._.exec-store-via-resolved
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
-- Once.CCC.Machine.FlatStackPtr._.exec-abstract
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
-- Once.CCC.Machine.FlatStackPtr._.exec-load-from-slot-with-value
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
-- Once.CCC.Machine.FlatStackPtr._.exec-restore-input-with-value
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
-- Once.CCC.Machine.FlatStackPtr._.exec-sigop-output
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
-- Once.CCC.Machine.FlatStackPtr._.exec-sigop-output-of
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
-- Once.CCC.Machine.FlatStackPtr._.pure-sigop-out-aux
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_pure'45'sigop'45'out'45'val_2648
      v1 v2 v3 v4
-- Once.CCC.Machine.FlatStackPtr._.structured-pure-sigop-output
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
-- Once.CCC.Machine.FlatStackPtr._.FlatState
d_FlatState_166 a0 = ()
-- Once.CCC.Machine.FlatStackPtr._.do-branch
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
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_156
-- Once.CCC.Machine.FlatStackPtr._.flat-exec-instr
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
-- Once.CCC.Machine.FlatStackPtr._.FlatState.falloc
d_falloc_252 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_falloc_252 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.FlatState.floc
d_floc_254 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_floc_254 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.FlatState.fpc
d_fpc_256 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> Integer
d_fpc_256 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_74 (coe v0)
-- Once.CCC.Machine.FlatStackPtr.StackPtrOK
d_StackPtrOK_258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_StackPtrOK_258 = erased
-- Once.CCC.Machine.FlatStackPtr.StackPtrOK?
d_StackPtrOK'63'_272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_StackPtrOK'63'_272 = erased
-- Once.CCC.Machine.FlatStackPtr.SPInv
d_SPInv_288 a0 a1 a2 = ()
data T_SPInv_288
  = C_mkStackPtrWF_322 (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
                        AgdaAny)
                       (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny)
                       (AgdaAny -> Integer -> AgdaAny)
-- Once.CCC.Machine.FlatStackPtr.SPInv.sp-regs
d_sp'45'regs_310 ::
  T_SPInv_288 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
d_sp'45'regs_310 v0
  = case coe v0 of
      C_mkStackPtrWF_322 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.SPInv.sp-heap
d_sp'45'heap_314 ::
  T_SPInv_288 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny
d_sp'45'heap_314 v0
  = case coe v0 of
      C_mkStackPtrWF_322 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.SPInv.sp-stack
d_sp'45'stack_320 :: T_SPInv_288 -> AgdaAny -> Integer -> AgdaAny
d_sp'45'stack_320 v0
  = case coe v0 of
      C_mkStackPtrWF_322 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.StackPtrWF
d_StackPtrWF_324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_StackPtrWF_324 = erased
-- Once.CCC.Machine.FlatStackPtr.stack-ptr-frame
d_stack'45'ptr'45'frame_336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  Integer ->
  T_SPInv_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'ptr'45'frame_336 = erased
-- Once.CCC.Machine.FlatStackPtr.stack-ptr-suc-live
d_stack'45'ptr'45'suc'45'live_358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  Integer ->
  T_SPInv_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_stack'45'ptr'45'suc'45'live_358 ~v0 ~v1 v2 ~v3 ~v4 v5 ~v6
  = du_stack'45'ptr'45'suc'45'live_358 v2 v5
du_stack'45'ptr'45'suc'45'live_358 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  T_SPInv_288 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_stack'45'ptr'45'suc'45'live_358 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_sp'45'regs_310 v1 v0)
-- Once.CCC.Machine.FlatStackPtr.stack-ptr-live
d_stack'45'ptr'45'live_380 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  Integer ->
  T_SPInv_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_stack'45'ptr'45'live_380 ~v0 ~v1 v2 ~v3 v4 v5 ~v6
  = du_stack'45'ptr'45'live_380 v2 v4 v5
du_stack'45'ptr'45'live_380 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Integer -> T_SPInv_288 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_stack'45'ptr'45'live_380 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
         (coe addInt (coe (1 :: Integer)) (coe v1)))
      (coe du_stack'45'ptr'45'suc'45'live_358 (coe v0) (coe v2))
-- Once.CCC.Machine.FlatStackPtr.readReg-write
d_readReg'45'write_402 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_126 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_readReg'45'write_402 ~v0 ~v1 v2 v3 ~v4
  = du_readReg'45'write_402 v2 v3
du_readReg'45'write_402 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_readReg'45'write_402 v0 v1
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
d_sp'45'halt_510 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  Bool -> T_SPInv_288 -> T_SPInv_288
d_sp'45'halt_510 ~v0 ~v1 ~v2 ~v3 v4 = du_sp'45'halt_510 v4
du_sp'45'halt_510 :: T_SPInv_288 -> T_SPInv_288
du_sp'45'halt_510 v0 = coe v0
-- Once.CCC.Machine.FlatStackPtr.sp-write-reg
d_sp'45'write'45'reg_528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_288 -> T_SPInv_288
d_sp'45'write'45'reg_528 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_sp'45'write'45'reg_528 v3 v5 v6
du_sp'45'write'45'reg_528 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> T_SPInv_288 -> T_SPInv_288
du_sp'45'write'45'reg_528 v0 v1 v2
  = coe
      C_mkStackPtrWF_322
      (coe
         (\ v3 ->
            coe
              du_go_550 (coe v1) (coe v2) (coe v3)
              (coe du_readReg'45'write_402 (coe v0) (coe v3))))
      (coe (\ v3 -> coe d_sp'45'heap_314 v2 v3))
      (coe (\ v3 v4 -> coe d_sp'45'stack_320 v2 v3 v4))
-- Once.CCC.Machine.FlatStackPtr._.anchor
d_anchor_546 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny ->
  T_SPInv_288 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_anchor_546 = erased
-- Once.CCC.Machine.FlatStackPtr._.go
d_go_550 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny ->
  T_SPInv_288 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_go_550 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 = du_go_550 v5 v6 v7 v8
du_go_550 ::
  AgdaAny ->
  T_SPInv_288 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_go_550 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> coe d_sp'45'regs_310 v1 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-write-reg-halt
d_sp'45'write'45'reg'45'halt_598 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Bool -> AgdaAny -> T_SPInv_288 -> T_SPInv_288
d_sp'45'write'45'reg'45'halt_598 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du_sp'45'write'45'reg'45'halt_598 v3 v6 v7
du_sp'45'write'45'reg'45'halt_598 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> T_SPInv_288 -> T_SPInv_288
du_sp'45'write'45'reg'45'halt_598 v0 v1 v2
  = coe du_sp'45'write'45'reg_528 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.FlatStackPtr.sp-wsm-aux
d_sp'45'wsm'45'aux_634 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
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
d_sp'45'wsm'45'aux_634 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 ~v9 ~v10
                       v11 v12
  = du_sp'45'wsm'45'aux_634 v7 v8 v11 v12
du_sp'45'wsm'45'aux_634 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_sp'45'wsm'45'aux_634 v0 v1 v2 v3
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
d_sp'45'whm'45'aux_674 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_sp'45'whm'45'aux_674 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 v9
  = du_sp'45'whm'45'aux_674 v5 v8 v9
du_sp'45'whm'45'aux_674 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_sp'45'whm'45'aux_674 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe seq (coe v4) (coe v2)
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-write-stack
d_sp'45'write'45'stack_702 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_288 -> T_SPInv_288
d_sp'45'write'45'stack_702 v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du_sp'45'write'45'stack_702 v0 v3 v4 v6 v7
du_sp'45'write'45'stack_702 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> AgdaAny -> T_SPInv_288 -> T_SPInv_288
du_sp'45'write'45'stack_702 v0 v1 v2 v3 v4
  = coe
      C_mkStackPtrWF_322 (coe d_sp'45'regs_310 (coe v4))
      (coe d_sp'45'heap_314 (coe v4))
      (coe
         (\ v5 v6 ->
            coe
              du_sp'45'wsm'45'aux_634
              (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__84 v0 v1 v5)
              (coe
                 MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v2) (coe v6))
              (coe d_sp'45'stack_320 v4 v5 v6) (coe v3)))
-- Once.CCC.Machine.FlatStackPtr.sp-write-heap
d_sp'45'write'45'heap_730 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_288 -> T_SPInv_288
d_sp'45'write'45'heap_730 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_sp'45'write'45'heap_730 v3 v5 v6
du_sp'45'write'45'heap_730 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> T_SPInv_288 -> T_SPInv_288
du_sp'45'write'45'heap_730 v0 v1 v2
  = coe
      C_mkStackPtrWF_322 (coe d_sp'45'regs_310 (coe v2))
      (coe
         (\ v3 ->
            coe
              du_sp'45'whm'45'aux_674
              (coe
                 MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__80 (coe v0)
                 (coe v3))
              (coe d_sp'45'heap_314 v2 v3) (coe v1)))
      (coe d_sp'45'stack_320 (coe v2))
-- Once.CCC.Machine.FlatStackPtr.writeLoc-dyn
d_writeLoc'45'dyn_752 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'dyn_752 = erased
-- Once.CCC.Machine.FlatStackPtr.sp-write-mem
d_sp'45'write'45'mem_796 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_288 -> T_SPInv_288
d_sp'45'write'45'mem_796 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_sp'45'write'45'mem_796 v0 v3 v5 v6
du_sp'45'write'45'mem_796 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_SPInv_288 -> T_SPInv_288
du_sp'45'write'45'mem_796 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             du_sp'45'write'45'stack_702 (coe v0) (coe v4) (coe v5) (coe v2)
             (coe v3)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> coe du_sp'45'write'45'heap_730 (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-read-loc
d_sp'45'read'45'loc_830 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  T_SPInv_288 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
d_sp'45'read'45'loc_830 ~v0 ~v1 ~v2 v3 v4
  = du_sp'45'read'45'loc_830 v3 v4
du_sp'45'read'45'loc_830 ::
  T_SPInv_288 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
du_sp'45'read'45'loc_830 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe d_sp'45'stack_320 v0 v2 v3
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe d_sp'45'heap_314 v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-load-value
d_sp'45'load'45'value_858 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_288 -> T_SPInv_288
d_sp'45'load'45'value_858 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_sp'45'load'45'value_858 v3 v4 v5 v6
du_sp'45'load'45'value_858 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_288 -> T_SPInv_288
du_sp'45'load'45'value_858 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe du_sp'45'write'45'reg_528 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-load-resolved
d_sp'45'load'45'resolved_890 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_SPInv_288 -> T_SPInv_288
d_sp'45'load'45'resolved_890 ~v0 ~v1 v2 v3 v4 v5
  = du_sp'45'load'45'resolved_890 v2 v3 v4 v5
du_sp'45'load'45'resolved_890 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_SPInv_288 -> T_SPInv_288
du_sp'45'load'45'resolved_890 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_sp'45'load'45'value_858 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v0)
                (coe v4))
             (coe du_sp'45'read'45'loc_830 (coe v3) (coe v4)) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-load-suc-resolved
d_sp'45'load'45'suc'45'resolved_918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_SPInv_288 -> T_SPInv_288
d_sp'45'load'45'suc'45'resolved_918 ~v0 ~v1 v2 v3 v4 v5
  = du_sp'45'load'45'suc'45'resolved_918 v2 v3 v4 v5
du_sp'45'load'45'suc'45'resolved_918 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_SPInv_288 -> T_SPInv_288
du_sp'45'load'45'suc'45'resolved_918 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_sp'45'load'45'value_858 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v0)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v4)))
             (coe
                du_sp'45'read'45'loc_830 (coe v3)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v4)))
             (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-store-resolved
d_sp'45'store'45'resolved_946 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_288 -> T_SPInv_288
d_sp'45'store'45'resolved_946 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_sp'45'store'45'resolved_946 v0 v3 v5 v6
du_sp'45'store'45'resolved_946 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_SPInv_288 -> T_SPInv_288
du_sp'45'store'45'resolved_946 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_sp'45'write'45'mem_796 (coe v0) (coe v4) (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-store-suc-resolved
d_sp'45'store'45'suc'45'resolved_978 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_288 -> T_SPInv_288
d_sp'45'store'45'suc'45'resolved_978 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_sp'45'store'45'suc'45'resolved_978 v0 v3 v5 v6
du_sp'45'store'45'suc'45'resolved_978 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_SPInv_288 -> T_SPInv_288
du_sp'45'store'45'suc'45'resolved_978 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_sp'45'write'45'mem_796 (coe v0)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v4))
             (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-from-slot
d_sp'45'from'45'slot_1008 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_288 -> T_SPInv_288
d_sp'45'from'45'slot_1008 ~v0 ~v1 ~v2 v3 v4 v5
  = du_sp'45'from'45'slot_1008 v3 v4 v5
du_sp'45'from'45'slot_1008 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_288 -> T_SPInv_288
du_sp'45'from'45'slot_1008 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_sp'45'write'45'reg_528
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) (coe v1)
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-restore
d_sp'45'restore_1034 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_288 -> T_SPInv_288
d_sp'45'restore_1034 ~v0 ~v1 ~v2 v3 v4 v5
  = du_sp'45'restore_1034 v3 v4 v5
du_sp'45'restore_1034 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> T_SPInv_288 -> T_SPInv_288
du_sp'45'restore_1034 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_sp'45'write'45'reg_528
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v1)
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-pred
d_sp'45'pred_1060 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
d_sp'45'pred_1060 ~v0 ~v1 ~v2 v3 = du_sp'45'pred_1060 v3
du_sp'45'pred_1060 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
du_sp'45'pred_1060 v0
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
d_sp'45'succ_1098 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
d_sp'45'succ_1098 ~v0 ~v1 ~v2 v3 = du_sp'45'succ_1098 v3
du_sp'45'succ_1098 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
du_sp'45'succ_1098 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatStackPtr.sp-reg-op
d_sp'45'reg'45'op_1132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_506 ->
  T_SPInv_288 -> T_SPInv_288
d_sp'45'reg'45'op_1132 ~v0 ~v1 v2 v3 v4
  = du_sp'45'reg'45'op_1132 v2 v3 v4
du_sp'45'reg'45'op_1132 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_506 ->
  T_SPInv_288 -> T_SPInv_288
du_sp'45'reg'45'op_1132 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_508
        -> coe
             du_sp'45'write'45'reg_528
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_510
        -> coe
             du_sp'45'write'45'reg_528
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_512
        -> coe
             du_sp'45'write'45'reg_528
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe
                du_sp'45'pred_1060
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v0))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)))
             (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_514
        -> coe
             du_sp'45'write'45'reg_528
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)
             (coe
                d_sp'45'regs_310 v2
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64))
             (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_516
        -> coe
             du_sp'45'write'45'reg_528
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_518
        -> coe
             du_sp'45'write'45'reg_528
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64)
             (coe
                du_sp'45'succ_1098
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v0))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64)))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.structured-pure-sigop-no-stack
d_structured'45'pure'45'sigop'45'no'45'stack_1182
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.FlatStackPtr.structured-pure-sigop-no-stack"
-- Once.CCC.Machine.FlatStackPtr.sigop-output-ok
d_sigop'45'output'45'ok_1196 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 -> AgdaAny
d_sigop'45'output'45'ok_1196 v0 v1 v2 v3 v4 v5 v6
  = coe
      d_go_1240 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe MAlonzo.Code.Once.SigOp.Info.du_effect_212 (coe v5))
-- Once.CCC.Machine.FlatStackPtr._.pov
d_pov_1218 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 -> Maybe AgdaAny -> AgdaAny
d_pov_1218 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_pov_1218 v8
du_pov_1218 :: Maybe AgdaAny -> AgdaAny
du_pov_1218 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatStackPtr._.aux
d_aux_1230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
d_aux_1230 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> case coe v8 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
               -> coe
                    du_pov_1218
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2606 (coe v3)
                       (coe v10) (coe v6))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    du_pov_1218
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg'45'typed_2600
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v6))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             d_structured'45'pure'45'sigop'45'no'45'stack_1182 v0 v1 v2 v3 v4 v5
             v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr._.go
d_go_1240 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 -> AgdaAny
d_go_1240 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_124
        -> coe
             d_aux_1230 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v6)
             (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_204 (coe v4))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1396
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v6))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
      MAlonzo.Code.Once.SigOp.Info.C_Emits_126
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.SigOp.Info.C_Halts_128
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-abstract
d_sp'45'abstract_1250 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  AgdaAny ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  T_SPInv_288 -> T_SPInv_288
d_sp'45'abstract_1250 v0 v1 v2 v3 ~v4 v5 v6
  = du_sp'45'abstract_1250 v0 v1 v2 v3 v5 v6
du_sp'45'abstract_1250 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  T_SPInv_288 -> T_SPInv_288
du_sp'45'abstract_1250 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240
        -> coe
             du_sp'45'write'45'reg_528
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                d_sp'45'regs_310 v5
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242
        -> coe
             du_sp'45'write'45'reg_528
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
             (coe
                d_sp'45'regs_310 v5
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2244
        -> coe
             du_sp'45'write'45'reg_528
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58)
             (coe
                d_sp'45'regs_310 v5
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2246
        -> coe
             du_sp'45'write'45'reg_528
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                d_sp'45'regs_310 v5
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2248
        -> coe
             du_sp'45'load'45'resolved_890 (coe v2)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1396
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2250
        -> coe
             du_sp'45'load'45'suc'45'resolved_918 (coe v2)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1396
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2252 v6
        -> coe
             du_sp'45'from'45'slot_1008
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                      (coe v3))
                   (coe v6)))
             (coe
                du_sp'45'read'45'loc_830 (coe v5)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                      (coe v3))
                   (coe v6)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2254 v6
        -> coe
             du_sp'45'write'45'mem_796 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                   (coe v3))
                (coe v6))
             (coe
                d_sp'45'regs_310 v5
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2256
        -> coe
             du_sp'45'store'45'resolved_946 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1396
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                d_sp'45'regs_310 v5
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2258
        -> coe
             du_sp'45'store'45'suc'45'resolved_978 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1396
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                d_sp'45'regs_310 v5
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2260 v6
        -> coe
             du_sp'45'write'45'reg_528
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe v4 v6 erased))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2262 v6
        -> coe
             du_sp'45'restore_1034
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                      (coe v3))
                   (coe v6)))
             (coe
                du_sp'45'read'45'loc_830 (coe v5)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                      (coe v3))
                   (coe v6)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2268 v6
        -> coe v5
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2274
        -> coe v5
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2276 v6
        -> coe v5
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2278 v6
        -> coe
             du_sp'45'write'45'mem_796 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                   (coe v3))
                (coe v6))
             (coe
                d_sp'45'regs_310 v5
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2280 v6
        -> coe
             du_sp'45'from'45'slot_1008
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                      (coe v3))
                   (coe v6)))
             (coe
                du_sp'45'read'45'loc_830 (coe v5)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                      (coe v3))
                   (coe v6)))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2282 v6
        -> coe v5
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2288 v6 v7 v8
        -> coe
             du_sp'45'write'45'reg'45'halt_598
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe
                d_sigop'45'output'45'ok_1196 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2816
                         (coe v0) (coe v1) (coe v2) (coe v3))))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackSlot_148
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v2)))
                (coe v6) (coe v7) (coe v8) (coe v2))
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2292 v6 v7 v8
        -> coe
             du_sp'45'write'45'reg_528
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2294 v6
        -> coe
             du_sp'45'write'45'reg_528
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2296
        -> coe v5
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2298 v6
        -> coe
             du_sp'45'write'45'reg_528
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2302 v6
        -> coe
             du_sp'45'write'45'reg_528
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2306 v6
        -> coe du_sp'45'reg'45'op_1132 (coe v2) (coe v6) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2308 v6
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-jump
d_sp'45'jump_1620 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_SPInv_288 -> T_SPInv_288
d_sp'45'jump_1620 ~v0 v1 ~v2 v3 = du_sp'45'jump_1620 v1 v3
du_sp'45'jump_1620 :: Maybe Integer -> T_SPInv_288 -> T_SPInv_288
du_sp'45'jump_1620 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatStackPtr.sp-branch
d_sp'45'branch_1640 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_SPInv_288 -> T_SPInv_288
d_sp'45'branch_1640 v0 v1 v2 v3 ~v4 v5
  = du_sp'45'branch_1640 v0 v1 v2 v3 v5
du_sp'45'branch_1640 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_SPInv_288 -> T_SPInv_288
du_sp'45'branch_1640 v0 v1 v2 v3 v4
  = if coe v1
      then coe
             du_sp'45'jump_1620
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_142 (coe v0)
                (coe v3) (coe v2))
             (coe v4)
      else coe v4
-- Once.CCC.Machine.FlatStackPtr.flat-stack-ptr
d_flat'45'stack'45'ptr_1666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  AgdaAny ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  T_SPInv_288 -> T_SPInv_288
d_flat'45'stack'45'ptr_1666 v0 v1 v2 v3 ~v4 v5 v6
  = du_flat'45'stack'45'ptr_1666 v0 v1 v2 v3 v5 v6
du_flat'45'stack'45'ptr_1666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  T_SPInv_288 -> T_SPInv_288
du_flat'45'stack'45'ptr_1666 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2244
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2246
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2248
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2250
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2252 v6
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2254 v6
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2256
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2258
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2260 v6
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2262 v6
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2268 v6
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2274
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2276 v6
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2278 v6
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2280 v6
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2282 v6
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2288 v6 v7 v8
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2292 v6 v7 v8
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2294 v6
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2296
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2298 v6
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2302 v6
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2306 v6
        -> coe
             du_sp'45'abstract_1250 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v3))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2308 v6
        -> case coe v6 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2230 v7 -> coe v5
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2232 v7
               -> coe
                    du_sp'45'jump_1620
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_142 (coe v0)
                       (coe v2) (coe v7))
                    (coe v5)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2234 v7
               -> coe
                    du_sp'45'branch_1640 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_78
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552
                             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3)))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)))
                    (coe v7) (coe v2) (coe v5)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2236 v7
               -> coe
                    du_sp'45'branch_1640 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_80
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_92
                          (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3))))
                    (coe v7) (coe v2) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
