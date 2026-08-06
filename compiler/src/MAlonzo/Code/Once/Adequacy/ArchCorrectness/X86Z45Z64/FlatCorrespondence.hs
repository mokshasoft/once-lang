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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Semantics.FloatBits
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.readLoc
d_readLoc_16 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_readLoc_16 ~v0 ~v1 = du_readLoc_16
du_readLoc_16 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_readLoc_16
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.writeHeapMem
d_writeHeapMem_18 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_writeHeapMem_18 ~v0 ~v1 = du_writeHeapMem_18
du_writeHeapMem_18 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_writeHeapMem_18
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem_850
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.writeLoc
d_writeLoc_20 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_writeLoc_20 v0 ~v1 = du_writeLoc_20 v0
du_writeLoc_20 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_writeLoc_20 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_878 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.writeLocToHeap
d_writeLocToHeap_26 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_writeLocToHeap_26 ~v0 ~v1 = du_writeLocToHeap_26
du_writeLocToHeap_26 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_writeLocToHeap_26
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_870
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.writeLocToStack
d_writeLocToStack_28 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_writeLocToStack_28 v0 ~v1 = du_writeLocToStack_28 v0
du_writeLocToStack_28 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_writeLocToStack_28 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLocToStack_860 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_32 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'load'45'suc'45'via'45'resolved_32 ~v0 ~v1
  = du_exec'45'load'45'suc'45'via'45'resolved_32
du_exec'45'load'45'suc'45'via'45'resolved_32 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_exec'45'load'45'suc'45'via'45'resolved_32
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'suc'45'via'45'resolved_1570
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_34 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'load'45'via'45'resolved_34 ~v0 ~v1
  = du_exec'45'load'45'via'45'resolved_34
du_exec'45'load'45'via'45'resolved_34 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_exec'45'load'45'via'45'resolved_34
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'via'45'resolved_1532
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_38 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'store'45'suc'45'via'45'resolved_38 v0 ~v1
  = du_exec'45'store'45'suc'45'via'45'resolved_38 v0
du_exec'45'store'45'suc'45'via'45'resolved_38 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_exec'45'store'45'suc'45'via'45'resolved_38 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'suc'45'via'45'resolved_1582
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_40 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'store'45'via'45'resolved_40 v0 ~v1
  = du_exec'45'store'45'via'45'resolved_40 v0
du_exec'45'store'45'via'45'resolved_40 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_exec'45'store'45'via'45'resolved_40 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'via'45'resolved_1544
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatState
d_FlatState_46 a0 a1 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.do-ret
d_do'45'ret_72 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'ret_72 ~v0 ~v1 = du_do'45'ret_72
du_do'45'ret_72 ::
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'ret_72
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'ret_714
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.do-thunk
d_do'45'thunk_86 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'thunk_86 v0 ~v1 = du_do'45'thunk_86 v0
du_do'45'thunk_86 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'thunk_86 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'thunk_848 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.enter-call
d_enter'45'call_88 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_enter'45'call_88 v0 ~v1 = du_enter'45'call_88 v0
du_enter'45'call_88 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_enter'45'call_88 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'call_534 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.flat-exec-instr
d_flat'45'exec'45'instr_140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_140 v0 ~v1
  = du_flat'45'exec'45'instr_140 v0
du_flat'45'exec'45'instr_140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'exec'45'instr_140 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1076
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.leave-frame
d_leave'45'frame_178 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_leave'45'frame_178 ~v0 ~v1 = du_leave'45'frame_178
du_leave'45'frame_178 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_leave'45'frame_178
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame_550
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.leave-frame-aux
d_leave'45'frame'45'aux_180 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_leave'45'frame'45'aux_180 ~v0 ~v1 = du_leave'45'frame'45'aux_180
du_leave'45'frame'45'aux_180 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_leave'45'frame'45'aux_180
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame'45'aux_538
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sv-is-zero
d_sv'45'is'45'zero_204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
d_sv'45'is'45'zero_204 ~v0 ~v1 = du_sv'45'is'45'zero_204
du_sv'45'is'45'zero_204 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
du_sv'45'is'45'zero_204
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_100
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatState.falloc
d_falloc_222 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_falloc_222 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatState.fclosure
d_fclosure_224 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fclosure_224 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_88 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatState.floc
d_floc_226 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_floc_226 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatState.fpc
d_fpc_228 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_228 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_84 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatState.fret
d_fret_230 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_230 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_86 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.shift-frame
d_shift'45'frame_234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> Integer -> AgdaAny
d_shift'45'frame_234 v0 ~v1 = du_shift'45'frame_234 v0
du_shift'45'frame_234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> AgdaAny
du_shift'45'frame_234 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_102 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sv-below
d_sv'45'below_238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_sv'45'below_238 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.svm-below
d_svm'45'below_240 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_svm'45'below_240 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.exec-abstract
d_exec'45'abstract_244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_244 v0 ~v1 = du_exec'45'abstract_244 v0
du_exec'45'abstract_244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'abstract_244 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2870
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.Frame
d_Frame_252 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> ()
d_Frame_252 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.frame-base
d_frame'45'base_254 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> Integer
d_frame'45'base_254 v0 ~v1 = du_frame'45'base_254 v0
du_frame'45'base_254 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer
du_frame'45'base_254 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.slot-addr
d_slot'45'addr_260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> Integer -> Integer
d_slot'45'addr_260 v0 ~v1 = du_slot'45'addr_260 v0
du_slot'45'addr_260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> Integer
du_slot'45'addr_260 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_slot'45'addr_88 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView
d_HeapView_264 a0 a1 = ()
data T_HeapView_264
  = C_mkHV_318 (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                Integer)
               Integer (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer)
               (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
               Integer MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView.haddr
d_haddr_292 ::
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_haddr_292 v0
  = case coe v0 of
      C_mkHV_318 v1 v3 v4 v7 v8 v9 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView.HDom
d_HDom_294 ::
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> ()
d_HDom_294 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView.hfront
d_hfront_296 :: T_HeapView_264 -> Integer
d_hfront_296 v0
  = case coe v0 of
      C_mkHV_318 v1 v3 v4 v7 v8 v9 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView.caddr
d_caddr_298 ::
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_caddr_298 v0
  = case coe v0 of
      C_mkHV_318 v1 v3 v4 v7 v8 v9 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView.haddr-suc
d_haddr'45'suc_302 ::
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_302 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView.haddr-inj
d_haddr'45'inj_308 ::
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_308 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView.dom-below
d_dom'45'below_312 ::
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_312 v0
  = case coe v0 of
      C_mkHV_318 v1 v3 v4 v7 v8 v9 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView.lo
d_lo_314 :: T_HeapView_264 -> Integer
d_lo_314 v0
  = case coe v0 of
      C_mkHV_318 v1 v3 v4 v7 v8 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView.front-lo
d_front'45'lo_316 ::
  T_HeapView_264 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo_316 v0
  = case coe v0 of
      C_mkHV_318 v1 v3 v4 v7 v8 v9 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.lit-word
d_lit'45'word_320 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer
d_lit'45'word_320 ~v0 ~v1 v2 = du_lit'45'word_320 v2
du_lit'45'word_320 :: Integer -> Integer
du_lit'45'word_320 v0 = coe v0
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.AddrMap
d_AddrMap_324 a0 a1 = ()
data T_AddrMap_324
  = C_mkAddrMap_334 (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                     Integer)
                    (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.AddrMap.hmap
d_hmap_330 ::
  T_AddrMap_324 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_hmap_330 v0
  = case coe v0 of
      C_mkAddrMap_334 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.AddrMap.cmap
d_cmap_332 ::
  T_AddrMap_324 -> MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_cmap_332 v0
  = case coe v0 of
      C_mkAddrMap_334 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.enc-sv-at
d_enc'45'sv'45'at_336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
d_enc'45'sv'45'at_336 v0 ~v1 v2 v3
  = du_enc'45'sv'45'at_336 v0 v2 v3
du_enc'45'sv'45'at_336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AddrMap_324 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
du_enc'45'sv'45'at_336 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v3
        -> case coe v3 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
               -> coe
                    MAlonzo.Code.Once.CCC.FrameSemantics.d_slot'45'addr_88 v0 v4 v5
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
               -> coe d_hmap_330 v1 v4
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v3 -> coe v3
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C_fits'45'int_198 -> coe v5
             MAlonzo.Code.Once.Type.C_fits'45'float_200
               -> coe
                    MAlonzo.Code.Once.Semantics.FloatBits.d_float'45'bits_6 (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v3
        -> coe d_cmap_332 v1 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.enc-maybe-at
d_enc'45'maybe'45'at_364 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
d_enc'45'maybe'45'at_364 v0 ~v1 v2 v3
  = du_enc'45'maybe'45'at_364 v0 v2 v3
du_enc'45'maybe'45'at_364 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AddrMap_324 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
du_enc'45'maybe'45'at_364 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe du_enc'45'sv'45'at_336 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.amap
d_amap_372 :: T_HeapView_264 -> T_AddrMap_324
d_amap_372 v0
  = coe
      C_mkAddrMap_334 (coe d_haddr_292 (coe v0))
      (coe d_caddr_298 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.enc-sv
d_enc'45'sv_376 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
d_enc'45'sv_376 v0 ~v1 v2 = du_enc'45'sv_376 v0 v2
du_enc'45'sv_376 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
du_enc'45'sv_376 v0 v1
  = coe
      du_enc'45'sv'45'at_336 (coe v0)
      (coe
         C_mkAddrMap_334 (coe d_haddr_292 (coe v1))
         (coe d_caddr_298 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.enc-maybe
d_enc'45'maybe_380 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
d_enc'45'maybe_380 v0 ~v1 v2 = du_enc'45'maybe_380 v0 v2
du_enc'45'maybe_380 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_264 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
du_enc'45'maybe_380 v0 v1
  = coe
      du_enc'45'maybe'45'at_364 (coe v0)
      (coe
         C_mkAddrMap_334 (coe d_haddr_292 (coe v1))
         (coe d_caddr_298 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.frames-of
d_frames'45'of_384 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_frames'45'of_384 ~v0 ~v1 v2 = du_frames'45'of_384 v2
du_frames'45'of_384 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_frames'45'of_384 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.Window
d_Window_388 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  AgdaAny -> Integer -> ()
d_Window_388 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.StackWindows
d_StackWindows_404 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_StackWindows_404 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.GapNext
d_GapNext_428 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_GapNext_428 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.RetAddrs
d_RetAddrs_438 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [Integer] -> ()
d_RetAddrs_438 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ret-head
d_ret'45'head_484 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_ret'45'head_484 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 v11
  = du_ret'45'head_484 v9 v11
du_ret'45'head_484 :: [Integer] -> AgdaAny -> AgdaAny
du_ret'45'head_484 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe seq (coe v5) (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr
d_FlatCorr_540 a0 a1 a2 a3 a4 = ()
data T_FlatCorr_540
  = C_constructor_636 (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                       AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                       MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny)
                      (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny)
                      MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                      MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.rdi-eq
d_rdi'45'eq_592 ::
  T_FlatCorr_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45'eq_592 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.rsi-eq
d_rsi'45'eq_594 ::
  T_FlatCorr_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rsi'45'eq_594 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.rax-eq
d_rax'45'eq_596 ::
  T_FlatCorr_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rax'45'eq_596 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.rbx-eq
d_rbx'45'eq_598 ::
  T_FlatCorr_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rbx'45'eq_598 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.r14-eq
d_r14'45'eq_600 ::
  T_FlatCorr_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r14'45'eq_600 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.r12-eq
d_r12'45'eq_602 ::
  T_FlatCorr_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r12'45'eq_602 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.halt-eq
d_halt'45'eq_604 ::
  T_FlatCorr_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45'eq_604 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.rsp-eq
d_rsp'45'eq_606 ::
  T_FlatCorr_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rsp'45'eq_606 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.r15-eq
d_r15'45'eq_608 ::
  T_FlatCorr_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r15'45'eq_608 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.dom-fresh
d_dom'45'fresh_612 ::
  T_FlatCorr_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'fresh_612 v0
  = case coe v0 of
      C_constructor_636 v10 v11 v12 v14 v16 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.dom-written
d_dom'45'written_618 ::
  T_FlatCorr_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_dom'45'written_618 v0
  = case coe v0 of
      C_constructor_636 v10 v11 v12 v14 v16 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.dom-sized
d_dom'45'sized_622 ::
  T_FlatCorr_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_dom'45'sized_622 v0
  = case coe v0 of
      C_constructor_636 v10 v11 v12 v14 v16 -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.heap-eq
d_heap'45'eq_626 ::
  T_FlatCorr_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'eq_626 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.lo-le
d_lo'45'le_628 ::
  T_FlatCorr_540 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'le_628 v0
  = case coe v0 of
      C_constructor_636 v10 v11 v12 v14 v16 -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.untouched
d_untouched_632 ::
  T_FlatCorr_540 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched_632 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.stack-eq
d_stack'45'eq_634 ::
  T_FlatCorr_540 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'eq_634 v0
  = case coe v0 of
      C_constructor_636 v10 v11 v12 v14 v16 -> coe v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.win-at
d_win'45'at_654 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_win'45'at_654 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.win-off
d_win'45'off_700 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_win'45'off_700 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.stack-eq-win
d_stack'45'eq'45'win_736 ::
  T_FlatCorr_540 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'eq'45'win_736 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.stack-eq-cur
d_stack'45'eq'45'cur_750 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'eq'45'cur_750 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sep
d_sep_766 ::
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sep_766 v0 ~v1 ~v2 v3 = du_sep_766 v0 v3
du_sep_766 ::
  T_HeapView_264 ->
  T_FlatCorr_540 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sep_766 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe d_front'45'lo_316 (coe v0)) (coe d_lo'45'le_628 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.descend-view
d_descend'45'view_776 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_HeapView_264
d_descend'45'view_776 ~v0 ~v1 v2 v3 ~v4 v5
  = du_descend'45'view_776 v2 v3 v5
du_descend'45'view_776 ::
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_HeapView_264
du_descend'45'view_776 v0 v1 v2
  = coe
      C_mkHV_318 (d_haddr_292 (coe v0)) (d_hfront_296 (coe v0))
      (d_caddr_298 (coe v0)) (d_dom'45'below_312 (coe v0)) v1 v2
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.untouched-descend
d_untouched'45'descend_800 ::
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_FlatCorr_540 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'descend_800 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-mov-to-output
d_sim'45'mov'45'to'45'output_822 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 -> T_FlatCorr_540
d_sim'45'mov'45'to'45'output_822 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'mov'45'to'45'output_822 v5
du_sim'45'mov'45'to'45'output_822 ::
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'mov'45'to'45'output_822 v0
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v0))
      (d_dom'45'written_618 (coe v0)) (d_dom'45'sized_622 (coe v0))
      (d_lo'45'le_628 (coe v0)) (d_stack'45'eq_634 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-mov-to-input
d_sim'45'mov'45'to'45'input_838 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 -> T_FlatCorr_540
d_sim'45'mov'45'to'45'input_838 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'mov'45'to'45'input_838 v5
du_sim'45'mov'45'to'45'input_838 ::
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'mov'45'to'45'input_838 v0
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v0))
      (d_dom'45'written_618 (coe v0)) (d_dom'45'sized_622 (coe v0))
      (d_lo'45'le_628 (coe v0)) (d_stack'45'eq_634 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-mov-input2-to-output
d_sim'45'mov'45'input2'45'to'45'output_854 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 -> T_FlatCorr_540
d_sim'45'mov'45'input2'45'to'45'output_854 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'mov'45'input2'45'to'45'output_854 v5
du_sim'45'mov'45'input2'45'to'45'output_854 ::
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'mov'45'input2'45'to'45'output_854 v0
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v0))
      (d_dom'45'written_618 (coe v0)) (d_dom'45'sized_622 (coe v0))
      (d_lo'45'le_628 (coe v0)) (d_stack'45'eq_634 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-mov-output-to-input2
d_sim'45'mov'45'output'45'to'45'input2_870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 -> T_FlatCorr_540
d_sim'45'mov'45'output'45'to'45'input2_870 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'mov'45'output'45'to'45'input2_870 v5
du_sim'45'mov'45'output'45'to'45'input2_870 ::
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'mov'45'output'45'to'45'input2_870 v0
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v0))
      (d_dom'45'written_618 (coe v0)) (d_dom'45'sized_622 (coe v0))
      (d_lo'45'le_628 (coe v0)) (d_stack'45'eq_634 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-tag-lit
d_sim'45'load'45'tag'45'lit_888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 -> T_FlatCorr_540
d_sim'45'load'45'tag'45'lit_888 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_sim'45'load'45'tag'45'lit_888 v6
du_sim'45'load'45'tag'45'lit_888 ::
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'load'45'tag'45'lit_888 v0
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v0))
      (d_dom'45'written_618 (coe v0)) (d_dom'45'sized_622 (coe v0))
      (d_lo'45'le_628 (coe v0)) (d_stack'45'eq_634 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-reg-scratch-one
d_sim'45'reg'45'scratch'45'one_906 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 -> T_FlatCorr_540
d_sim'45'reg'45'scratch'45'one_906 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'reg'45'scratch'45'one_906 v5
du_sim'45'reg'45'scratch'45'one_906 ::
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'reg'45'scratch'45'one_906 v0
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v0))
      (d_dom'45'written_618 (coe v0)) (d_dom'45'sized_622 (coe v0))
      (d_lo'45'le_628 (coe v0)) (d_stack'45'eq_634 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-reg-scratch-zero
d_sim'45'reg'45'scratch'45'zero_922 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 -> T_FlatCorr_540
d_sim'45'reg'45'scratch'45'zero_922 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'reg'45'scratch'45'zero_922 v5
du_sim'45'reg'45'scratch'45'zero_922 ::
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'reg'45'scratch'45'zero_922 v0
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v0))
      (d_dom'45'written_618 (coe v0)) (d_dom'45'sized_622 (coe v0))
      (d_lo'45'le_628 (coe v0)) (d_stack'45'eq_634 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-reg-count-zero
d_sim'45'reg'45'count'45'zero_938 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 -> T_FlatCorr_540
d_sim'45'reg'45'count'45'zero_938 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'reg'45'count'45'zero_938 v5
du_sim'45'reg'45'count'45'zero_938 ::
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'reg'45'count'45'zero_938 v0
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v0))
      (d_dom'45'written_618 (coe v0)) (d_dom'45'sized_622 (coe v0))
      (d_lo'45'le_628 (coe v0)) (d_stack'45'eq_634 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-reg-scratch-load-count
d_sim'45'reg'45'scratch'45'load'45'count_954 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 -> T_FlatCorr_540
d_sim'45'reg'45'scratch'45'load'45'count_954 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'reg'45'scratch'45'load'45'count_954 v5
du_sim'45'reg'45'scratch'45'load'45'count_954 ::
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'reg'45'scratch'45'load'45'count_954 v0
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v0))
      (d_dom'45'written_618 (coe v0)) (d_dom'45'sized_622 (coe v0))
      (d_lo'45'le_628 (coe v0)) (d_stack'45'eq_634 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sv-tag-zero
d_sv'45'tag'45'zero_966 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sv'45'tag'45'zero_966 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.enc-zero
d_enc'45'zero_974 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'zero_974 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-indirect-suc
d_sim'45'load'45'indirect'45'suc_988 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_540
d_sim'45'load'45'indirect'45'suc_988 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
                                     ~v8 ~v9
  = du_sim'45'load'45'indirect'45'suc_988 v7
du_sim'45'load'45'indirect'45'suc_988 ::
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'load'45'indirect'45'suc_988 v0
  = coe du_corr'45'clean_1024 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_1010 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_1010 v0 ~v1 v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9
  = du_xpost_1010 v0 v2 v4 v6
du_xpost_1010 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_1010 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v3))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
         (coe du_enc'45'sv_376 v0 v1 v2))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v3))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v3))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v3)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v3))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cleanFlat
d_cleanFlat_1012 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_1012 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_cleanFlat_1012 v4 v5
du_cleanFlat_1012 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_1012 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_90
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_168
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_84 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_86 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_88 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.floc-eq
d_floc'45'eq_1014 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_1014 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_1020 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_1020 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_1024 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_540
d_corr'45'clean_1024 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9
  = du_corr'45'clean_1024 v7
du_corr'45'clean_1024 :: T_FlatCorr_540 -> T_FlatCorr_540
du_corr'45'clean_1024 v0
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v0))
      (d_dom'45'written_618 (coe v0)) (d_dom'45'sized_622 (coe v0))
      (d_lo'45'le_628 (coe v0)) (d_stack'45'eq_634 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-indirect
d_sim'45'load'45'indirect_1038 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_540
d_sim'45'load'45'indirect_1038 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
                               ~v9
  = du_sim'45'load'45'indirect_1038 v7
du_sim'45'load'45'indirect_1038 :: T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'load'45'indirect_1038 v0
  = coe du_corr'45'clean_1074 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_1060 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_1060 v0 ~v1 v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9
  = du_xpost_1060 v0 v2 v4 v6
du_xpost_1060 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_1060 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v3))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
         (coe du_enc'45'sv_376 v0 v1 v2))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v3))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v3))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v3)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v3))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cleanFlat
d_cleanFlat_1062 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_1062 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_cleanFlat_1062 v4 v5
du_cleanFlat_1062 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_1062 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_90
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_168
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_84 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_86 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_88 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.floc-eq
d_floc'45'eq_1064 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_1064 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_1070 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_1070 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_1074 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_540
d_corr'45'clean_1074 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9
  = du_corr'45'clean_1074 v7
du_corr'45'clean_1074 :: T_FlatCorr_540 -> T_FlatCorr_540
du_corr'45'clean_1074 v0
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v0))
      (d_dom'45'written_618 (coe v0)) (d_dom'45'sized_622 (coe v0))
      (d_lo'45'le_628 (coe v0)) (d_stack'45'eq_634 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-from-slot
d_sim'45'load'45'from'45'slot_1088 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_540
d_sim'45'load'45'from'45'slot_1088 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
                                   ~v8
  = du_sim'45'load'45'from'45'slot_1088 v7
du_sim'45'load'45'from'45'slot_1088 ::
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'load'45'from'45'slot_1088 v0
  = coe du_corr'45'clean_1120 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_1108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_1108 v0 ~v1 v2 ~v3 v4 ~v5 v6 ~v7 ~v8
  = du_xpost_1108 v0 v2 v4 v6
du_xpost_1108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_1108 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v3))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
         (coe du_enc'45'sv_376 v0 v1 v2))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v3))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v3))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v3)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v3))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.ex-eq
d_ex'45'eq_1110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ex'45'eq_1110 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cleanFlat
d_cleanFlat_1114 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_1114 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8
  = du_cleanFlat_1114 v4 v5
du_cleanFlat_1114 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_1114 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_90
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_168
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_84 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_86 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_88 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_1116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_1116 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_1120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_540
d_corr'45'clean_1120 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_corr'45'clean_1120 v7
du_corr'45'clean_1120 :: T_FlatCorr_540 -> T_FlatCorr_540
du_corr'45'clean_1120 v0
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v0))
      (d_dom'45'written_618 (coe v0)) (d_dom'45'sized_622 (coe v0))
      (d_lo'45'le_628 (coe v0)) (d_stack'45'eq_634 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.≡ᵇ-refl
d_'8801''7495''45'refl_1126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_1126 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.≢→≡ᵇfalse
d_'8802''8594''8801''7495'false_1134 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8802''8594''8801''7495'false_1134 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.untouched-write
d_untouched'45'write_1158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'write_1158 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.untouched-heap-store
d_untouched'45'heap'45'store_1188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny ->
  T_FlatCorr_540 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'heap'45'store_1188 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.untouched-stack-store
d_untouched'45'stack'45'store_1226 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_FlatCorr_540 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'stack'45'store_1226 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.store-heap-eq
d_store'45'heap'45'eq_1262 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'heap'45'eq_1262 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.store-dom-written
d_store'45'dom'45'written_1350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_store'45'dom'45'written_1350 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 v9
                               v10
  = du_store'45'dom'45'written_1350 v3 v6 v7 v8 v9 v10
du_store'45'dom'45'written_1350 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_store'45'dom'45'written_1350 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.Memory.HeapAddress.du_'8799'HL'45'aux_62
              (let v6
                     = coe
                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                         erased
                         (\ v6 ->
                            coe
                              MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                              (coe
                                 MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                                 (coe
                                    MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48
                                    (coe v0))))
                         (coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                            (coe
                               eqInt
                               (coe
                                  MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                                  (coe
                                     MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48
                                     (coe v0)))
                               (coe
                                  MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                                  (coe
                                     MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48
                                     (coe v3))))
                            (coe
                               MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                               (coe
                                  eqInt
                                  (coe
                                     MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                                     (coe
                                        MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48
                                        (coe v0)))
                                  (coe
                                     MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                                     (coe
                                        MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48
                                        (coe v3)))))) in
               coe
                 (case coe v6 of
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                      -> if coe v7
                           then coe
                                  seq (coe v8)
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                     (coe v7)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
                           else coe
                                  seq (coe v8)
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                     (coe v7)
                                     (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                    _ -> MAlonzo.RTE.mazUnreachableError))
              (coe
                 MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
                 (coe
                    MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50 (coe v0))
                 (coe
                    MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50
                    (coe v3))) in
    coe
      (case coe v6 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
           -> if coe v7
                then coe seq (coe v8) (coe v1)
                else coe seq (coe v8) (coe v2 v3 v4 v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.read-write-hit
d_read'45'write'45'hit_1412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'write'45'hit_1412 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.read-write-miss
d_read'45'write'45'miss_1432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'write'45'miss_1432 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.windows-reanchor
d_windows'45'reanchor_1464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'reanchor_1464 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           v10 v11
  = du_windows'45'reanchor_1464 v10 v11
du_windows'45'reanchor_1464 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'reanchor_1464 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             seq (coe v3)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.windows-lower
d_windows'45'lower_1494 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_windows'45'lower_1494 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
  = du_windows'45'lower_1494 v7 v8 v9
du_windows'45'lower_1494 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_windows'45'lower_1494 v0 v1 v2
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v3 v4
        -> coe
             seq (coe v3)
             (case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v1)
                             (coe v5))
                          (coe v6))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.windows-forget
d_windows'45'forget_1540 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (AgdaAny ->
   Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
d_windows'45'forget_1540 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
  = du_windows'45'forget_1540 v7 v8 v9
du_windows'45'forget_1540 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (AgdaAny ->
   Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
du_windows'45'forget_1540 v0 v1 v2
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        (\ v11 v12 v13 v14 ->
                                           coe v9 v11 v12 v13 (coe v1 v5 v11 v13 v14)))
                                     (coe du_windows'45'forget_1540 (coe v4) erased (coe v10)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.windows-leave
d_windows'45'leave_1594 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'leave_1594 v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7
  = du_windows'45'leave_1594 v0 v5 v7
du_windows'45'leave_1594 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'leave_1594 v0 v1 v2
  = coe
      du_go_1614 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
         (coe v1))
      (coe v2)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.go
d_go_1614 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_1614 v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9 v10
  = du_go_1614 v0 v5 v8 v10
du_go_1614 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_1614 v0 v1 v2 v3
  = case coe v2 of
      [] -> coe v3
      (:) v4 v5
        -> coe
             seq (coe v4)
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v7 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                         -> case coe v9 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                -> coe
                                     seq (coe v11)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                           (coe v6)
                                           (coe
                                              MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86
                                                    v0
                                                    (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                                                       (coe v1))))
                                              (coe v10)))
                                        (coe v11))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.windows-above
d_windows'45'above_1660 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
d_windows'45'above_1660 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
                        v11
  = du_windows'45'above_1660 v8 v11
du_windows'45'above_1660 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny -> AgdaAny
du_windows'45'above_1660 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v2 v3
        -> coe
             seq (coe v2)
             (case coe v1 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                 (coe du_windows'45'above_1660 (coe v3) (coe v7)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.up
d_up_1710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_up_1710 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 v13
          ~v14 ~v15
  = du_up_1710 v0 v8 v13
du_up_1710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_up_1710 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v2)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0 v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.windows-write-below
d_windows'45'write'45'below_1742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_windows'45'write'45'below_1742 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
                                 ~v9
  = du_windows'45'write'45'below_1742 v8
du_windows'45'write'45'below_1742 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny -> AgdaAny
du_windows'45'write'45'below_1742 v0
  = coe du_windows'45'above_1660 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.windows-heap-store
d_windows'45'heap'45'store_1784 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny -> T_FlatCorr_540 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'heap'45'store_1784 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_windows'45'heap'45'store_1784 v3 v8
du_windows'45'heap'45'store_1784 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_540 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'heap'45'store_1784 v0 v1
  = coe
      du_windows'45'write'45'below_1742
      (coe
         du_frames'45'of_384
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v0)))
      (d_stack'45'eq_634 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-store-indirect
d_sim'45'store'45'indirect_1808 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_540
d_sim'45'store'45'indirect_1808 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 ~v7 v8 ~v9
  = du_sim'45'store'45'indirect_1808 v3 v4 v6 v8
du_sim'45'store'45'indirect_1808 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_540 -> AgdaAny -> T_FlatCorr_540
du_sim'45'store'45'indirect_1808 v0 v1 v2 v3
  = coe du_corr'45'clean_1844 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.v
d_v_1830 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_v_1830 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_v_1830 v4
du_v_1830 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_v_1830 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_1832 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_1832 v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_xpost_1832 v0 v2 v3 v4 v5
du_xpost_1832 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_1832 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v4))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeMem_188
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
            (coe v4))
         (coe d_haddr_292 v1 v2)
         (coe du_enc'45'sv_376 v0 v1 (coe du_v_1830 (coe v3))))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v4))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v4)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v4))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cleanFlat
d_cleanFlat_1834 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_1834 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_cleanFlat_1834 v3 v4
du_cleanFlat_1834 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_1834 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_90
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_870
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1))
         (coe v0) (coe du_v_1830 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_84 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_86 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_88 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.floc-eq
d_floc'45'eq_1836 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_1836 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_1840 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_1840 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_1844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_540
d_corr'45'clean_1844 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 ~v7 v8 ~v9
  = du_corr'45'clean_1844 v3 v4 v6 v8
du_corr'45'clean_1844 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_540 -> AgdaAny -> T_FlatCorr_540
du_corr'45'clean_1844 v0 v1 v2 v3
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v2))
      (coe
         du_store'45'dom'45'written_1350 (coe v0) (coe v3)
         (coe d_dom'45'written_618 (coe v2)))
      (d_dom'45'sized_622 (coe v2)) (d_lo'45'le_628 (coe v2))
      (coe du_windows'45'heap'45'store_1784 (coe v1) (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-store-indirect-suc
d_sim'45'store'45'indirect'45'suc_1856 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_540
d_sim'45'store'45'indirect'45'suc_1856 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 ~v7
                                       v8 ~v9
  = du_sim'45'store'45'indirect'45'suc_1856 v3 v4 v6 v8
du_sim'45'store'45'indirect'45'suc_1856 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_540 -> AgdaAny -> T_FlatCorr_540
du_sim'45'store'45'indirect'45'suc_1856 v0 v1 v2 v3
  = coe du_corr'45'clean_1892 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.v
d_v_1878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_v_1878 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_v_1878 v4
du_v_1878 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_v_1878 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_1880 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_1880 v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_xpost_1880 v0 v2 v3 v4 v5
du_xpost_1880 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_1880 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v4))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeMem_188
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
            (coe v4))
         (coe
            d_haddr_292 v1
            (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v2)))
         (coe du_enc'45'sv_376 v0 v1 (coe du_v_1878 (coe v3))))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v4))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v4)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v4))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cleanFlat
d_cleanFlat_1882 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_1882 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_cleanFlat_1882 v3 v4
du_cleanFlat_1882 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_1882 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_90
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_870
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1))
         (coe MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v0))
         (coe du_v_1878 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_84 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_86 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_88 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.floc-eq
d_floc'45'eq_1884 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_1884 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_1888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_1888 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_1892 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_540
d_corr'45'clean_1892 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 ~v7 v8 ~v9
  = du_corr'45'clean_1892 v3 v4 v6 v8
du_corr'45'clean_1892 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_540 -> AgdaAny -> T_FlatCorr_540
du_corr'45'clean_1892 v0 v1 v2 v3
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v2))
      (coe
         du_store'45'dom'45'written_1350
         (coe MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v0))
         (coe v3) (coe d_dom'45'written_618 (coe v2)))
      (d_dom'45'sized_622 (coe v2)) (d_lo'45'le_628 (coe v2))
      (coe du_windows'45'heap'45'store_1784 (coe v1) (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-restore-input
d_sim'45'restore'45'input_1906 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_540
d_sim'45'restore'45'input_1906 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_sim'45'restore'45'input_1906 v7
du_sim'45'restore'45'input_1906 :: T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'restore'45'input_1906 v0
  = coe du_corr'45'clean_1938 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_1926 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_1926 v0 ~v1 v2 ~v3 v4 ~v5 v6 ~v7 ~v8
  = du_xpost_1926 v0 v2 v4 v6
du_xpost_1926 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_1926 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v3))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20)
         (coe du_enc'45'sv_376 v0 v1 v2))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v3))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v3))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v3)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v3))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.ex-eq
d_ex'45'eq_1928 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ex'45'eq_1928 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cleanFlat
d_cleanFlat_1932 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_1932 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8
  = du_cleanFlat_1932 v4 v5
du_cleanFlat_1932 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_1932 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_90
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_168
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_84 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_86 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_88 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_1934 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_1934 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_1938 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_540
d_corr'45'clean_1938 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_corr'45'clean_1938 v7
du_corr'45'clean_1938 :: T_FlatCorr_540 -> T_FlatCorr_540
du_corr'45'clean_1938 v0
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v0))
      (d_dom'45'written_618 (coe v0)) (d_dom'45'sized_622 (coe v0))
      (d_lo'45'le_628 (coe v0)) (d_stack'45'eq_634 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.slot-addr-inj
d_slot'45'addr'45'inj_1948 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'inj_1948 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.atstack-slot-inj
d_atstack'45'slot'45'inj_1964 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atstack'45'slot'45'inj_1964 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.atstack-frame-inj
d_atstack'45'frame'45'inj_1976 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atstack'45'frame'45'inj_1976 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.store-slot-heap-eq
d_store'45'slot'45'heap'45'eq_1994 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'slot'45'heap'45'eq_1994 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.store-slot-stack-eq
d_store'45'slot'45'stack'45'eq_2044 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  (Integer -> Maybe Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'slot'45'stack'45'eq_2044 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.just-inj
d_just'45'inj_2080 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  (Integer -> Maybe Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_2080 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.go
d_go_2082 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  (Integer -> Maybe Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_2082 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.windows-slot-store
d_windows'45'slot'45'store_2122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  (Integer -> Maybe Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'slot'45'store_2122 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                ~v9 v10 ~v11 v12
  = du_windows'45'slot'45'store_2122 v10 v12
du_windows'45'slot'45'store_2122 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'slot'45'store_2122 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                       (coe du_windows'45'above_1660 (coe v0) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.waddr
d_waddr_2154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  (Integer -> Maybe Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> Integer
d_waddr_2154 v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14
  = du_waddr_2154 v0 v5 v7
du_waddr_2154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> Integer
du_waddr_2154 v0 v1 v2
  = coe
      addInt
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0 v1)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_slot'45'to'45'disp_10
         (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.mem'
d_mem''_2156 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  (Integer -> Maybe Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> Integer -> Maybe Integer
d_mem''_2156 v0 ~v1 v2 v3 ~v4 v5 ~v6 v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
             ~v14
  = du_mem''_2156 v0 v2 v3 v5 v7 v8
du_mem''_2156 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AddrMap_324 ->
  (Integer -> Maybe Integer) ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer -> Maybe Integer
du_mem''_2156 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeMem_188
      (coe v2) (coe du_waddr_2154 (coe v0) (coe v3) (coe v4))
      (coe du_enc'45'sv'45'at_336 (coe v0) (coe v1) (coe v5))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.w<fl
d_w'60'fl_2158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  (Integer -> Maybe Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_w'60'fl_2158 v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 ~v8 ~v9 ~v10 v11 ~v12
               ~v13 ~v14
  = du_w'60'fl_2158 v0 v5 v6 v7 v11
du_w'60'fl_2158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_w'60'fl_2158 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3714
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0 v1)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'737''45''60'_4240
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80)
         (coe v3) (coe v2) (coe v4))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.base<
d_base'60'_2162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  (Integer -> Maybe Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_base'60'_2162 v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 ~v8 ~v9 ~v10 v11 ~v12
                ~v13 ~v14 v15 v16
  = du_base'60'_2162 v0 v5 v6 v7 v11 v15 v16
du_base'60'_2162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_base'60'_2162 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'60''45'trans'737'_6714
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0 v1)
      (addInt
         (coe
            MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
            (\ v7 v8 -> v8)
            (\ v7 ->
               mulInt
                 (coe v7)
                 (coe
                    MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80))
            (0 :: Integer) v2)
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0 v1))
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0 v5)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'60'm'43'n_3736
         (coe MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0 v1)
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'737''45''60'_4240
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80)
            (coe (0 :: Integer)) (coe v2)
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'60''45'trans'691'_6712
               (0 :: Integer) v3 v2 (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
               v4)))
      v6
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-store-at-slot
d_sim'45'store'45'at'45'slot_2190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FlatCorr_540
d_sim'45'store'45'at'45'slot_2190 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 ~v8
  = du_sim'45'store'45'at'45'slot_2190 v4 v6
du_sim'45'store'45'at'45'slot_2190 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'store'45'at'45'slot_2190 v0 v1
  = coe du_corr'45'clean_2218 (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.base
d_base_2210 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer
d_base_2210 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 = du_base_2210 v5
du_base_2210 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer
du_base_2210 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.Out
d_Out_2212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_Out_2212 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 = du_Out_2212 v4
du_Out_2212 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_Out_2212 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cf
d_cf_2214 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
d_cf_2214 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 = du_cf_2214 v4
du_cf_2214 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny
du_cf_2214 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_2216 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_2216 v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8
  = du_xpost_2216 v0 v2 v3 v4 v5
du_xpost_2216 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_2216 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v4))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeMem_188
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
            (coe v4))
         (coe
            addInt (coe du_base_2210 (coe v4))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_slot'45'to'45'disp_10
               (coe v2)))
         (coe du_enc'45'sv_376 v0 v1 (coe du_Out_2212 (coe v3))))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v4))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v4)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v4))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_2218 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FlatCorr_540
d_corr'45'clean_2218 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 ~v8
  = du_corr'45'clean_2218 v4 v6
du_corr'45'clean_2218 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_540 -> T_FlatCorr_540
du_corr'45'clean_2218 v0 v1
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v1))
      (d_dom'45'written_618 (coe v1)) (d_dom'45'sized_622 (coe v1))
      (d_lo'45'le_628 (coe v1))
      (coe
         du_windows'45'slot'45'store_2122
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v0)))
         (coe d_stack'45'eq_634 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-alloc-stack
d_sim'45'alloc'45'stack_2240 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_FlatCorr_540
d_sim'45'alloc'45'stack_2240 v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7 ~v8 ~v9
                             ~v10 ~v11 v12 ~v13
  = du_sim'45'alloc'45'stack_2240 v0 v3 v5 v7 v12
du_sim'45'alloc'45'stack_2240 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_FlatCorr_540
du_sim'45'alloc'45'stack_2240 v0 v1 v2 v3 v4
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v3))
      (d_dom'45'written_618 (coe v3)) (d_dom'45'sized_622 (coe v3)) v4
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
            (coe
               du_windows'45'reanchor_1464
               (coe du_tail'45'le_2304 (coe v0) (coe v1) (coe v2))
               (coe d_stack'45'eq_634 (coe v3)))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cf
d_cf_2270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_cf_2270 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13
  = du_cf_2270 v5
du_cf_2270 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny
du_cf_2270 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.newbase
d_newbase_2272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_newbase_2272 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.stk
d_stk_2282 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stk_2282 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.tail-le
d_tail'45'le_2304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_tail'45'le_2304 v0 ~v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13
  = du_tail'45'le_2304 v0 v3 v5
du_tail'45'le_2304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_tail'45'le_2304 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0
            (coe
               MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_102 v0
               (coe du_cf_2270 (coe v2)) v1))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_82 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-thunk
d_sim'45'thunk_2328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_FlatCorr_540
d_sim'45'thunk_2328 v0 ~v1 ~v2 v3 ~v4 ~v5 v6 ~v7 v8 ~v9 ~v10 ~v11
                    v12 ~v13
  = du_sim'45'thunk_2328 v0 v3 v6 v8 v12
du_sim'45'thunk_2328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_FlatCorr_540
du_sim'45'thunk_2328 v0 v1 v2 v3 v4
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v3))
      (d_dom'45'written_618 (coe v3)) (d_dom'45'sized_622 (coe v3)) v4
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
            (coe
               du_windows'45'forget_1540
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
                  (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v2)))
               erased
               (coe
                  du_windows'45'lower_1494
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
                     (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v2)))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                     (coe du_tail'45'le_2418 (coe v0) (coe v1) (coe v2))
                     (coe
                        MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                        (coe
                           MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0
                           (coe du_cf_2358 (coe v2)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                        (coe d_stack'45'eq_634 (coe v3))))))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cf
d_cf_2358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_cf_2358 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13
  = du_cf_2358 v6
du_cf_2358 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny
du_cf_2358 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.nothing≢just
d_nothing'8802'just_2364 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nothing'8802'just_2364 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.head-window
d_head'45'window_2370 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_head'45'window_2370 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.newbase
d_newbase_2412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_newbase_2412 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.tail-le
d_tail'45'le_2418 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_tail'45'le_2418 v0 ~v1 ~v2 v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13
  = du_tail'45'le_2418 v0 v3 v6
du_tail'45'le_2418 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_tail'45'le_2418 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0
            (coe
               MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_102 v0
               (coe du_cf_2358 (coe v2)) v1))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_82 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-call
d_sim'45'call_2448 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_FlatCorr_540
d_sim'45'call_2448 v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 ~v10 ~v11
                   v12 ~v13
  = du_sim'45'call_2448 v0 v6 v7 v8 v12
du_sim'45'call_2448 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_FlatCorr_540
du_sim'45'call_2448 v0 v1 v2 v3 v4
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v3))
      (d_dom'45'written_618 (coe v3)) (d_dom'45'sized_622 (coe v3)) v4
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
            (coe
               du_windows'45'reanchor_1464
               (coe du_tail'45'floor_2488 (coe v0) (coe v1) (coe v2))
               (coe
                  du_windows'45'above_1660
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe du_cf_2478 (coe v1))
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652
                           (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v1))))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
                        (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v1))))
                  (coe
                     du_windows'45'reanchor_1464
                     (coe
                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                        (coe
                           MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0
                           (coe du_cf_2478 (coe v1))))
                     (coe d_stack'45'eq_634 (coe v3)))))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cf
d_cf_2478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_cf_2478 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13
  = du_cf_2478 v6
du_cf_2478 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny
du_cf_2478 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.waddr
d_waddr_2480 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_waddr_2480 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13
  = du_waddr_2480 v7
du_waddr_2480 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer
du_waddr_2480 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
      (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.newbase
d_newbase_2482 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_newbase_2482 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.tail-floor
d_tail'45'floor_2488 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_tail'45'floor_2488 v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 ~v10 ~v11
                     ~v12 ~v13
  = du_tail'45'floor_2488 v0 v6 v7
du_tail'45'floor_2488 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_tail'45'floor_2488 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0
               (coe
                  MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_102 v0
                  (coe du_cf_2478 (coe v1)) (1 :: Integer)))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_82
               (coe (0 :: Integer)))))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_m'8760'n'8804'm_5184
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v2))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v2))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.w<base
d_w'60'base_2490 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_w'60'base_2490 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 ~v13
  = du_w'60'base_2490 v7
du_w'60'base_2490 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_w'60'base_2490 v0 = coe du_m'8760'n'60'm'8242'_2496 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._._.m∸n<m′
d_m'8760'n'60'm'8242'_2496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8760'n'60'm'8242'_2496 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9
                           ~v10 ~v11 ~v12 ~v13 ~v14
  = du_m'8760'n'60'm'8242'_2496 v7
du_m'8760'n'60'm'8242'_2496 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8760'n'60'm'8242'_2496 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'60'm'43'n_3736
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
               (coe v0))
            (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80)
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-dealloc-stack
d_sim'45'dealloc'45'stack_2544 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_540
d_sim'45'dealloc'45'stack_2544 v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 ~v8
  = du_sim'45'dealloc'45'stack_2544 v0 v5 v6 v7
du_sim'45'dealloc'45'stack_2544 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'dealloc'45'stack_2544 v0 v1 v2 v3
  = coe
      C_constructor_636 (\ v4 v5 -> coe d_dom'45'fresh_612 v3 v4 v5)
      (d_dom'45'written_618 (coe v3))
      (\ v4 v5 -> coe d_dom'45'sized_622 v3 v4 v5)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe d_lo'45'le_628 (coe v3))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v2))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))))
      (coe
         du_windows'45'leave_1594 (coe v0)
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v1))
         (coe d_stack'45'eq_634 (coe v3)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-ret
d_sim'45'ret_2588 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_540
d_sim'45'ret_2588 v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 ~v11 ~v12
  = du_sim'45'ret_2588 v0 v3 v8 v9 v10
du_sim'45'ret_2588 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'ret_2588 v0 v1 v2 v3 v4
  = coe
      C_constructor_636 (\ v5 v6 -> coe d_dom'45'fresh_612 v4 v5 v6)
      (d_dom'45'written_618 (coe v4))
      (\ v5 v6 -> coe d_dom'45'sized_622 v4 v5 v6)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe d_lo'45'le_628 (coe v4))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                     (coe v3))
                  (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)))
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
               (coe
                  addInt
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_82 (coe v1))
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                        (coe v3))
                     (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))))))
      (coe
         du_windows'45'leave_1594 (coe v0)
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v2))
         (coe d_stack'45'eq_634 (coe v4)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-const
d_sim'45'load'45'const_2636 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 -> T_FlatCorr_540
d_sim'45'load'45'const_2636 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_sim'45'load'45'const_2636 v6
du_sim'45'load'45'const_2636 :: T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'load'45'const_2636 v0
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v0))
      (d_dom'45'written_618 (coe v0)) (d_dom'45'sized_622 (coe v0))
      (d_lo'45'le_628 (coe v0)) (d_stack'45'eq_634 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-const-float
d_sim'45'load'45'const'45'float_2656 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 -> T_FlatCorr_540
d_sim'45'load'45'const'45'float_2656 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_sim'45'load'45'const'45'float_2656 v6
du_sim'45'load'45'const'45'float_2656 ::
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'load'45'const'45'float_2656 v0
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v0))
      (d_dom'45'written_618 (coe v0)) (d_dom'45'sized_622 (coe v0))
      (d_lo'45'le_628 (coe v0)) (d_stack'45'eq_634 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-code-addr
d_sim'45'load'45'code'45'addr_2678 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_540
d_sim'45'load'45'code'45'addr_2678 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
                                   ~v8
  = du_sim'45'load'45'code'45'addr_2678 v7
du_sim'45'load'45'code'45'addr_2678 ::
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'load'45'code'45'addr_2678 v0
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v0))
      (d_dom'45'written_618 (coe v0)) (d_dom'45'sized_622 (coe v0))
      (d_lo'45'le_628 (coe v0)) (d_stack'45'eq_634 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-save-closure-reg
d_sim'45'save'45'closure'45'reg_2700 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 -> T_FlatCorr_540
d_sim'45'save'45'closure'45'reg_2700 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'save'45'closure'45'reg_2700 v5
du_sim'45'save'45'closure'45'reg_2700 ::
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'save'45'closure'45'reg_2700 v0
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v0))
      (d_dom'45'written_618 (coe v0)) (d_dom'45'sized_622 (coe v0))
      (d_lo'45'le_628 (coe v0)) (d_stack'45'eq_634 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.inc-enc
d_inc'45'enc_2716 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inc'45'enc_2716 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.dec-enc
d_dec'45'enc_2726 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AddrMap_324 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dec'45'enc_2726 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-reg-count-inc
d_sim'45'reg'45'count'45'inc_2740 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_540
d_sim'45'reg'45'count'45'inc_2740 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
                                  ~v8
  = du_sim'45'reg'45'count'45'inc_2740 v7
du_sim'45'reg'45'count'45'inc_2740 ::
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'reg'45'count'45'inc_2740 v0
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v0))
      (d_dom'45'written_618 (coe v0)) (d_dom'45'sized_622 (coe v0))
      (d_lo'45'le_628 (coe v0)) (d_stack'45'eq_634 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-reg-scratch-dec
d_sim'45'reg'45'scratch'45'dec_2768 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_540
d_sim'45'reg'45'scratch'45'dec_2768 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
                                    ~v8
  = du_sim'45'reg'45'scratch'45'dec_2768 v7
du_sim'45'reg'45'scratch'45'dec_2768 ::
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'reg'45'scratch'45'dec_2768 v0
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v0))
      (d_dom'45'written_618 (coe v0)) (d_dom'45'sized_622 (coe v0))
      (d_lo'45'le_628 (coe v0)) (d_stack'45'eq_634 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ext-addr-aux
d_ext'45'addr'45'aux_2792 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
d_ext'45'addr'45'aux_2792 ~v0 ~v1 v2 v3 ~v4 v5
  = du_ext'45'addr'45'aux_2792 v2 v3 v5
du_ext'45'addr'45'aux_2792 ::
  T_HeapView_264 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
du_ext'45'addr'45'aux_2792 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    addInt (coe d_hfront_296 (coe v0))
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_slot'45'to'45'disp_10
                       (coe
                          MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50 (coe v1)))
             else coe seq (coe v4) (coe d_haddr_292 v0 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ext-addr
d_ext'45'addr_2810 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_ext'45'addr_2810 ~v0 ~v1 v2 v3 v4 = du_ext'45'addr_2810 v2 v3 v4
du_ext'45'addr_2810 ::
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
du_ext'45'addr_2810 v0 v1 v2
  = coe
      du_ext'45'addr'45'aux_2792 (coe v0) (coe v2)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48 (coe v2)))
         (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ExtDom
d_ExtDom_2826 a0 a1 a2 a3 a4 a5 = ()
data T_ExtDom_2826
  = C_ext'45'old_2836 AgdaAny |
    C_ext'45'fresh_2838 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ext-addr-old
d_ext'45'addr'45'old_2846 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'old_2846 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.go
d_go_2862 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_2862 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ext-addr-fresh
d_ext'45'addr'45'fresh_2872 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'fresh_2872 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.go
d_go_2888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_2888 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ext-addr-base
d_ext'45'addr'45'base_2896 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'base_2896 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.+-not-<
d_'43''45'not'45''60'_2906 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'43''45'not'45''60'_2906 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ext-suc-aux
d_ext'45'suc'45'aux_2924 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'suc'45'aux_2924 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ext-suc
d_ext'45'suc_2950 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'suc_2950 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.extend-view
d_extend'45'view_2968 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_HeapView_264
d_extend'45'view_2968 ~v0 ~v1 v2 v3 v4 ~v5 v6
  = du_extend'45'view_2968 v2 v3 v4 v6
du_extend'45'view_2968 ::
  T_HeapView_264 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_HeapView_264
du_extend'45'view_2968 v0 v1 v2 v3
  = coe
      C_mkHV_318 (coe du_ext'45'addr_2810 (coe v0) (coe v1))
      (addInt
         (coe d_hfront_296 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_82 (coe v2)))
      (d_caddr_298 (coe v0)) (coe du_below_2986 (coe v0) (coe v2))
      (d_lo_314 (coe v0)) v3
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.below
d_below_2986 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_2826 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_below_2986 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 v7 v8
  = du_below_2986 v2 v4 v7 v8
du_below_2986 ::
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_2826 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_below_2986 v0 v1 v2 v3
  = case coe v3 of
      C_ext'45'old_2836 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'60''45'trans'737'_6714
             (coe d_haddr_292 v0 v2) (d_hfront_296 (coe v0))
             (addInt
                (coe d_hfront_296 (coe v0))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_82 (coe v1)))
             (coe d_dom'45'below_312 v0 v2 v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                (coe d_hfront_296 (coe v0)))
      C_ext'45'fresh_2838 v5
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3714
             (coe d_hfront_296 (coe v0))
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'737''45''60'_4240
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80)
                (coe
                   MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50 (coe v2))
                (coe v1) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cross
d_cross_3006 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_cross_3006 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.inj
d_inj_3024 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_2826 ->
  T_ExtDom_2826 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inj_3024 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._._.addr-eq
d_addr'45'eq_3074 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_addr'45'eq_3074 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._._.off-eq
d_off'45'eq_3076 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'eq_3076 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.enc-ext
d_enc'45'ext_3092 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'ext_3092 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.enc-ext-maybe
d_enc'45'ext'45'maybe_3176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'ext'45'maybe_3176 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.windows-enc-ext
d_windows'45'enc'45'ext_3226 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (AgdaAny -> Integer -> AgdaAny) -> AgdaAny -> AgdaAny
d_windows'45'enc'45'ext_3226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                             ~v9 v10 ~v11 v12
  = du_windows'45'enc'45'ext_3226 v10 v12
du_windows'45'enc'45'ext_3226 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny -> AgdaAny
du_windows'45'enc'45'ext_3226 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v2 v3
        -> coe
             seq (coe v2)
             (case coe v1 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                 (coe du_windows'45'enc'45'ext_3226 (coe v3) (coe v7)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-alloc-heap
d_sim'45'alloc'45'heap_3310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_FlatCorr_540
d_sim'45'alloc'45'heap_3310 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9
                            ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17
  = du_sim'45'alloc'45'heap_3310 v6 v8
du_sim'45'alloc'45'heap_3310 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'alloc'45'heap_3310 v0 v1
  = coe
      C_constructor_636 (coe du_df_3386 (coe v0) (coe v1))
      (\ v2 v3 v4 ->
         coe C_ext'45'old_2836 (coe d_dom'45'written_618 v1 v2 v3 erased))
      (coe du_ds_3354 (coe v0) (coe v1)) (d_lo'45'le_628 (coe v1))
      (coe
         du_windows'45'enc'45'ext_3226
         (coe
            du_frames'45'of_384
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v0)))
         (coe d_stack'45'eq_634 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.st
d_st_3348 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_st_3348 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17
  = du_st_3348 v6
du_st_3348 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
du_st_3348 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.dfr
d_dfr_3350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dfr_3350 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17
  = du_dfr_3350 v8
du_dfr_3350 ::
  T_FlatCorr_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_dfr_3350 v0 = coe d_dom'45'fresh_612 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.ds
d_ds_3354 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_ExtDom_2826
d_ds_3354 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 v18 v19
  = du_ds_3354 v6 v8 v18 v19
du_ds_3354 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_ExtDom_2826
du_ds_3354 v0 v1 v2 v3
  = coe
      du_go_3366 (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48 (coe v2)))
         (coe du_st_3348 (coe v0)))
      (coe v3)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._._.go
d_go_3366 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_ExtDom_2826
d_go_3366 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 v20 v21
  = du_go_3366 v8 v18 v20 v21
du_go_3366 ::
  T_FlatCorr_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_ExtDom_2826
du_go_3366 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe seq (coe v5) (coe C_ext'45'fresh_2838 v3)
             else coe
                    seq (coe v5)
                    (coe C_ext'45'old_2836 (coe d_dom'45'sized_622 v0 v1 v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.hv'
d_hv''_3374 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_HeapView_264
d_hv''_3374 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 ~v16 v17
  = du_hv''_3374 v2 v3 v6 v17
du_hv''_3374 ::
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_HeapView_264
du_hv''_3374 v0 v1 v2 v3
  = coe
      du_extend'45'view_2968 (coe v0) (coe du_st_3348 (coe v2)) (coe v1)
      (coe v3)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.fresh-x86
d_fresh'45'x86_3378 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fresh'45'x86_3378 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.df
d_df_3386 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_2826 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_df_3386 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 v18 v19
  = du_df_3386 v6 v8 v18 v19
du_df_3386 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_2826 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_df_3386 v0 v1 v2 v3
  = case coe v3 of
      C_ext'45'old_2836 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_m'60'n'8658'm'60'1'43'n_3204
             (coe du_dfr_3350 v1 v2 v4)
      C_ext'45'fresh_2838 v5
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe addInt (coe (1 :: Integer)) (coe du_st_3348 (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.hp
d_hp_3396 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_2826 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hp_3396 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-lea-slot
d_sim'45'lea'45'slot_3428 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 -> T_FlatCorr_540
d_sim'45'lea'45'slot_3428 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_sim'45'lea'45'slot_3428 v6
du_sim'45'lea'45'slot_3428 :: T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'lea'45'slot_3428 v0
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v0))
      (d_dom'45'written_618 (coe v0)) (d_dom'45'sized_622 (coe v0))
      (d_lo'45'le_628 (coe v0)) (d_stack'45'eq_634 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cf
d_cf_3444 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 -> AgdaAny
d_cf_3444 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du_cf_3444 v4
du_cf_3444 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny
du_cf_3444 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.addr-eq
d_addr'45'eq_3446 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_addr'45'eq_3446 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-indirect-stack
d_sim'45'load'45'indirect'45'stack_3464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_540
d_sim'45'load'45'indirect'45'stack_3464 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 v8 ~v9 ~v10
  = du_sim'45'load'45'indirect'45'stack_3464 v8
du_sim'45'load'45'indirect'45'stack_3464 ::
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'load'45'indirect'45'stack_3464 v0
  = coe du_corr'45'clean_3502 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_3488 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_3488 v0 ~v1 v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10
  = du_xpost_3488 v0 v2 v5 v7
du_xpost_3488 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_3488 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v3))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
         (coe du_enc'45'sv_376 v0 v1 v2))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v3))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v3))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v3)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v3))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cleanFlat
d_cleanFlat_3490 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_3490 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_cleanFlat_3490 v5 v6
du_cleanFlat_3490 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_3490 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_90
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_168
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_84 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_86 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_88 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.floc-eq
d_floc'45'eq_3492 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_3492 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_3498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_3498 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_3502 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_540
d_corr'45'clean_3502 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_corr'45'clean_3502 v8
du_corr'45'clean_3502 :: T_FlatCorr_540 -> T_FlatCorr_540
du_corr'45'clean_3502 v0
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v0))
      (d_dom'45'written_618 (coe v0)) (d_dom'45'sized_622 (coe v0))
      (d_lo'45'le_628 (coe v0)) (d_stack'45'eq_634 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-indirect-suc-stack
d_sim'45'load'45'indirect'45'suc'45'stack_3518 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_540
d_sim'45'load'45'indirect'45'suc'45'stack_3518 ~v0 ~v1 ~v2 ~v3 ~v4
                                               ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_sim'45'load'45'indirect'45'suc'45'stack_3518 v8
du_sim'45'load'45'indirect'45'suc'45'stack_3518 ::
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'load'45'indirect'45'suc'45'stack_3518 v0
  = coe du_corr'45'clean_3556 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_3542 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_3542 v0 ~v1 v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10
  = du_xpost_3542 v0 v2 v5 v7
du_xpost_3542 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_264 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_3542 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v3))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
         (coe du_enc'45'sv_376 v0 v1 v2))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v3))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v3))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v3)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v3))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cleanFlat
d_cleanFlat_3544 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_3544 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_cleanFlat_3544 v5 v6
du_cleanFlat_3544 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_3544 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_90
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_168
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_84 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_86 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_88 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.floc-eq
d_floc'45'eq_3546 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_3546 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_3552 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_3552 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_3556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_540
d_corr'45'clean_3556 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_corr'45'clean_3556 v8
du_corr'45'clean_3556 :: T_FlatCorr_540 -> T_FlatCorr_540
du_corr'45'clean_3556 v0
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v0))
      (d_dom'45'written_618 (coe v0)) (d_dom'45'sized_622 (coe v0))
      (d_lo'45'le_628 (coe v0)) (d_stack'45'eq_634 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-store-indirect-stack
d_sim'45'store'45'indirect'45'stack_3570 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FlatCorr_540
d_sim'45'store'45'indirect'45'stack_3570 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
                                         ~v7 ~v8 ~v9
  = du_sim'45'store'45'indirect'45'stack_3570 v4 v6
du_sim'45'store'45'indirect'45'stack_3570 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'store'45'indirect'45'stack_3570 v0 v1
  = coe du_corr'45'clean_3610 (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.base
d_base_3592 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer
d_base_3592 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_base_3592 v5
du_base_3592 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer
du_base_3592 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.Out
d_Out_3594 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_Out_3594 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_Out_3594 v4
du_Out_3594 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_Out_3594 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cf
d_cf_3596 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
d_cf_3596 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_cf_3596 v4
du_cf_3596 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny
du_cf_3596 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_3598 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_3598 v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_xpost_3598 v0 v2 v3 v4 v5
du_xpost_3598 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_3598 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v4))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeMem_188
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
            (coe v4))
         (coe
            addInt (coe du_base_3592 (coe v4))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_slot'45'to'45'disp_10
               (coe v2)))
         (coe du_enc'45'sv_376 v0 v1 (coe du_Out_3594 (coe v3))))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v4))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v4)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v4))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cleanFlat
d_cleanFlat_3600 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_3600 v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_cleanFlat_3600 v0 v3 v4
du_cleanFlat_3600 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_3600 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_90
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLocToStack_860 (coe v0)
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v2))
         (coe du_cf_3596 (coe v2)) (coe v1) (coe du_Out_3594 (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v2))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_84 (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_86 (coe v2))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_88 (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.floc-eq
d_floc'45'eq_3602 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_3602 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_3606 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_3606 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_3610 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FlatCorr_540
d_corr'45'clean_3610 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9
  = du_corr'45'clean_3610 v4 v6
du_corr'45'clean_3610 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_540 -> T_FlatCorr_540
du_corr'45'clean_3610 v0 v1
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v1))
      (d_dom'45'written_618 (coe v1)) (d_dom'45'sized_622 (coe v1))
      (d_lo'45'le_628 (coe v1))
      (coe
         du_windows'45'slot'45'store_2122
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v0)))
         (coe d_stack'45'eq_634 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-store-indirect-suc-stack
d_sim'45'store'45'indirect'45'suc'45'stack_3626 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FlatCorr_540
d_sim'45'store'45'indirect'45'suc'45'stack_3626 ~v0 ~v1 ~v2 ~v3 v4
                                                ~v5 v6 ~v7 ~v8 ~v9
  = du_sim'45'store'45'indirect'45'suc'45'stack_3626 v4 v6
du_sim'45'store'45'indirect'45'suc'45'stack_3626 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_540 -> T_FlatCorr_540
du_sim'45'store'45'indirect'45'suc'45'stack_3626 v0 v1
  = coe du_corr'45'clean_3666 (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.base
d_base_3648 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer
d_base_3648 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_base_3648 v5
du_base_3648 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer
du_base_3648 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.Out
d_Out_3650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_Out_3650 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_Out_3650 v4
du_Out_3650 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_Out_3650 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cf
d_cf_3652 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
d_cf_3652 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_cf_3652 v4
du_cf_3652 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny
du_cf_3652 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_3654 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_3654 v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_xpost_3654 v0 v2 v3 v4 v5
du_xpost_3654 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_3654 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v4))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeMem_188
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
            (coe v4))
         (coe
            addInt (coe du_base_3648 (coe v4))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_slot'45'to'45'disp_10
               (coe addInt (coe (1 :: Integer)) (coe v2))))
         (coe du_enc'45'sv_376 v0 v1 (coe du_Out_3650 (coe v3))))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v4))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v4)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v4))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cleanFlat
d_cleanFlat_3656 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_3656 v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_cleanFlat_3656 v0 v3 v4
du_cleanFlat_3656 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_3656 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_90
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLocToStack_860 (coe v0)
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v2))
         (coe du_cf_3652 (coe v2))
         (coe addInt (coe (1 :: Integer)) (coe v1))
         (coe du_Out_3650 (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v2))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_84 (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_86 (coe v2))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_88 (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.floc-eq
d_floc'45'eq_3658 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_3658 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_3662 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_3662 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_3666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_264 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FlatCorr_540
d_corr'45'clean_3666 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9
  = du_corr'45'clean_3666 v4 v6
du_corr'45'clean_3666 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_540 -> T_FlatCorr_540
du_corr'45'clean_3666 v0 v1
  = coe
      C_constructor_636 (d_dom'45'fresh_612 (coe v1))
      (d_dom'45'written_618 (coe v1)) (d_dom'45'sized_622 (coe v1))
      (d_lo'45'le_628 (coe v1))
      (coe
         du_windows'45'slot'45'store_2122
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v0)))
         (coe d_stack'45'eq_634 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ret-agree-above
d_ret'45'agree'45'above_3690 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Integer) ->
  T_AddrMap_324 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_ret'45'agree'45'above_3690 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
                             ~v10 v11 v12
  = du_ret'45'agree'45'above_3690 v8 v9 v11 v12
du_ret'45'agree'45'above_3690 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] -> AgdaAny -> AgdaAny -> AgdaAny
du_ret'45'agree'45'above_3690 v0 v1 v2 v3
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v4 v5
        -> case coe v0 of
             (:) v6 v7
               -> coe
                    seq (coe v6)
                    (case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                         -> case coe v9 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                -> case coe v3 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                       -> case coe v13 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   erased
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe v14)
                                                      (coe
                                                         du_ret'45'agree'45'above_3690 (coe v7)
                                                         (coe v5) (coe v11) (coe v15)))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ret-write-in-frame
d_ret'45'write'45'in'45'frame_3788 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Integer) ->
  T_AddrMap_324 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> AgdaAny
d_ret'45'write'45'in'45'frame_3788 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   ~v8 ~v9 ~v10 v11 v12 ~v13 v14 v15
  = du_ret'45'write'45'in'45'frame_3788 v11 v12 v14 v15
du_ret'45'write'45'in'45'frame_3788 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> AgdaAny
du_ret'45'write'45'in'45'frame_3788 v0 v1 v2 v3
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v4 v5
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> case coe v11 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                            (coe
                                               du_ret'45'agree'45'above_3690 (coe v0) (coe v5)
                                               (coe v9) (coe v13)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
