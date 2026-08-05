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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
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
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem_764
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
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_792 (coe v0)
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
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_784
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLocToStack_774 (coe v0)
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'suc'45'via'45'resolved_1478
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'via'45'resolved_1440
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'suc'45'via'45'resolved_1490
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'via'45'resolved_1452
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatState
d_FlatState_44 a0 a1 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.flat-exec-instr
d_flat'45'exec'45'instr_112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_flat'45'exec'45'instr_112 v0 ~v1
  = du_flat'45'exec'45'instr_112 v0
du_flat'45'exec'45'instr_112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_flat'45'exec'45'instr_112 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_570
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.leave-frame
d_leave'45'frame_140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_leave'45'frame_140 ~v0 ~v1 = du_leave'45'frame_140
du_leave'45'frame_140 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_leave'45'frame_140
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame_266
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.leave-frame-aux
d_leave'45'frame'45'aux_142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_leave'45'frame'45'aux_142 ~v0 ~v1 = du_leave'45'frame'45'aux_142
du_leave'45'frame'45'aux_142 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_leave'45'frame'45'aux_142
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame'45'aux_254
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sv-is-zero
d_sv'45'is'45'zero_166 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
d_sv'45'is'45'zero_166 ~v0 ~v1 = du_sv'45'is'45'zero_166
du_sv'45'is'45'zero_166 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
du_sv'45'is'45'zero_166
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_94
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatState.falloc
d_falloc_176 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_falloc_176 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatState.fclosure
d_fclosure_178 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fclosure_178 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_82 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatState.floc
d_floc_180 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_floc_180 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatState.fpc
d_fpc_182 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> Integer
d_fpc_182 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatState.fret
d_fret_184 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> [Integer]
d_fret_184 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.shift-frame
d_shift'45'frame_188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> Integer -> AgdaAny
d_shift'45'frame_188 v0 ~v1 = du_shift'45'frame_188 v0
du_shift'45'frame_188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> AgdaAny
du_shift'45'frame_188 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_102 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sv-below
d_sv'45'below_192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_sv'45'below_192 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.svm-below
d_svm'45'below_194 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_svm'45'below_194 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.exec-abstract
d_exec'45'abstract_198 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_198 v0 ~v1 = du_exec'45'abstract_198 v0
du_exec'45'abstract_198 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'abstract_198 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2766
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.Frame
d_Frame_206 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> ()
d_Frame_206 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.frame-base
d_frame'45'base_208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> Integer
d_frame'45'base_208 v0 ~v1 = du_frame'45'base_208 v0
du_frame'45'base_208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer
du_frame'45'base_208 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.slot-addr
d_slot'45'addr_214 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> Integer -> Integer
d_slot'45'addr_214 v0 ~v1 = du_slot'45'addr_214 v0
du_slot'45'addr_214 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> Integer
du_slot'45'addr_214 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_slot'45'addr_88 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView
d_HeapView_218 a0 a1 = ()
data T_HeapView_218
  = C_mkHV_268 (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                Integer)
               Integer
               (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
               Integer MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView.haddr
d_haddr_244 ::
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_haddr_244 v0
  = case coe v0 of
      C_mkHV_268 v1 v3 v6 v7 v8 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView.HDom
d_HDom_246 ::
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> ()
d_HDom_246 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView.hfront
d_hfront_248 :: T_HeapView_218 -> Integer
d_hfront_248 v0
  = case coe v0 of
      C_mkHV_268 v1 v3 v6 v7 v8 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView.haddr-suc
d_haddr'45'suc_252 ::
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_252 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView.haddr-inj
d_haddr'45'inj_258 ::
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_258 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView.dom-below
d_dom'45'below_262 ::
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_262 v0
  = case coe v0 of
      C_mkHV_268 v1 v3 v6 v7 v8 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView.lo
d_lo_264 :: T_HeapView_218 -> Integer
d_lo_264 v0
  = case coe v0 of
      C_mkHV_268 v1 v3 v6 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView.front-lo
d_front'45'lo_266 ::
  T_HeapView_218 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo_266 v0
  = case coe v0 of
      C_mkHV_268 v1 v3 v6 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.lit-word
d_lit'45'word_270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer
d_lit'45'word_270 ~v0 ~v1 v2 = du_lit'45'word_270 v2
du_lit'45'word_270 :: Integer -> Integer
du_lit'45'word_270 v0 = coe v0
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.AddrMap
d_AddrMap_274 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> ()
d_AddrMap_274 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.enc-sv-at
d_enc'45'sv'45'at_276 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
d_enc'45'sv'45'at_276 v0 ~v1 v2 v3
  = du_enc'45'sv'45'at_276 v0 v2 v3
du_enc'45'sv'45'at_276 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
du_enc'45'sv'45'at_276 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v3
        -> case coe v3 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
               -> coe
                    MAlonzo.Code.Once.CCC.FrameSemantics.d_slot'45'addr_88 v0 v4 v5
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
               -> coe v1 v4
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v3 -> coe v3
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C_fits'45'int_198 -> coe v5
             MAlonzo.Code.Once.Type.C_fits'45'float_200
               -> coe
                    MAlonzo.Code.Once.Semantics.FloatBits.d_float'45'bits_6 (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.enc-maybe-at
d_enc'45'maybe'45'at_304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
d_enc'45'maybe'45'at_304 v0 ~v1 v2 v3
  = du_enc'45'maybe'45'at_304 v0 v2 v3
du_enc'45'maybe'45'at_304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
du_enc'45'maybe'45'at_304 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe du_enc'45'sv'45'at_276 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.enc-sv
d_enc'45'sv_312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
d_enc'45'sv_312 v0 ~v1 v2 = du_enc'45'sv_312 v0 v2
du_enc'45'sv_312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
du_enc'45'sv_312 v0 v1
  = coe du_enc'45'sv'45'at_276 (coe v0) (coe d_haddr_244 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.enc-maybe
d_enc'45'maybe_316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
d_enc'45'maybe_316 v0 ~v1 v2 = du_enc'45'maybe_316 v0 v2
du_enc'45'maybe_316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_218 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
du_enc'45'maybe_316 v0 v1
  = coe du_enc'45'maybe'45'at_304 (coe v0) (coe d_haddr_244 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.frames-of
d_frames'45'of_320 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_frames'45'of_320 ~v0 ~v1 v2 = du_frames'45'of_320 v2
du_frames'45'of_320 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_frames'45'of_320 v0
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
d_Window_324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  AgdaAny -> Integer -> ()
d_Window_324 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.StackWindows
d_StackWindows_338 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_StackWindows_338 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr
d_FlatCorr_368 a0 a1 a2 a3 a4 = ()
data T_FlatCorr_368
  = C_constructor_460 (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                       AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                       MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny)
                      (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny)
                      MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                      MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.rdi-eq
d_rdi'45'eq_418 ::
  T_FlatCorr_368 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45'eq_418 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.rsi-eq
d_rsi'45'eq_420 ::
  T_FlatCorr_368 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rsi'45'eq_420 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.rax-eq
d_rax'45'eq_422 ::
  T_FlatCorr_368 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rax'45'eq_422 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.rbx-eq
d_rbx'45'eq_424 ::
  T_FlatCorr_368 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rbx'45'eq_424 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.r14-eq
d_r14'45'eq_426 ::
  T_FlatCorr_368 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r14'45'eq_426 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.halt-eq
d_halt'45'eq_428 ::
  T_FlatCorr_368 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45'eq_428 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.rsp-eq
d_rsp'45'eq_430 ::
  T_FlatCorr_368 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rsp'45'eq_430 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.r15-eq
d_r15'45'eq_432 ::
  T_FlatCorr_368 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r15'45'eq_432 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.dom-fresh
d_dom'45'fresh_436 ::
  T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'fresh_436 v0
  = case coe v0 of
      C_constructor_460 v9 v10 v11 v13 v15 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.dom-written
d_dom'45'written_442 ::
  T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_dom'45'written_442 v0
  = case coe v0 of
      C_constructor_460 v9 v10 v11 v13 v15 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.dom-sized
d_dom'45'sized_446 ::
  T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_dom'45'sized_446 v0
  = case coe v0 of
      C_constructor_460 v9 v10 v11 v13 v15 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.heap-eq
d_heap'45'eq_450 ::
  T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'eq_450 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.lo-le
d_lo'45'le_452 ::
  T_FlatCorr_368 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'le_452 v0
  = case coe v0 of
      C_constructor_460 v9 v10 v11 v13 v15 -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.untouched
d_untouched_456 ::
  T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched_456 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.stack-eq
d_stack'45'eq_458 ::
  T_FlatCorr_368 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'eq_458 v0
  = case coe v0 of
      C_constructor_460 v9 v10 v11 v13 v15 -> coe v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.win-at
d_win'45'at_476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
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
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_win'45'at_476 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.win-off
d_win'45'off_516 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
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
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_win'45'off_516 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.stack-eq-win
d_stack'45'eq'45'win_548 ::
  T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'eq'45'win_548 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.stack-eq-cur
d_stack'45'eq'45'cur_560 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'eq'45'cur_560 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sep
d_sep_576 ::
  T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sep_576 v0 ~v1 ~v2 v3 = du_sep_576 v0 v3
du_sep_576 ::
  T_HeapView_218 ->
  T_FlatCorr_368 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sep_576 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe d_front'45'lo_266 (coe v0)) (coe d_lo'45'le_452 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.descend-view
d_descend'45'view_586 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_HeapView_218
d_descend'45'view_586 ~v0 ~v1 v2 v3 ~v4 v5
  = du_descend'45'view_586 v2 v3 v5
du_descend'45'view_586 ::
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_HeapView_218
du_descend'45'view_586 v0 v1 v2
  = coe
      C_mkHV_268 (d_haddr_244 (coe v0)) (d_hfront_248 (coe v0))
      (d_dom'45'below_262 (coe v0)) v1 v2
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.untouched-descend
d_untouched'45'descend_610 ::
  T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'descend_610 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-mov-to-output
d_sim'45'mov'45'to'45'output_632 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 -> T_FlatCorr_368
d_sim'45'mov'45'to'45'output_632 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'mov'45'to'45'output_632 v5
du_sim'45'mov'45'to'45'output_632 ::
  T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'mov'45'to'45'output_632 v0
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v0))
      (d_dom'45'written_442 (coe v0)) (d_dom'45'sized_446 (coe v0))
      (d_lo'45'le_452 (coe v0)) (d_stack'45'eq_458 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-mov-to-input
d_sim'45'mov'45'to'45'input_648 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 -> T_FlatCorr_368
d_sim'45'mov'45'to'45'input_648 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'mov'45'to'45'input_648 v5
du_sim'45'mov'45'to'45'input_648 ::
  T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'mov'45'to'45'input_648 v0
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v0))
      (d_dom'45'written_442 (coe v0)) (d_dom'45'sized_446 (coe v0))
      (d_lo'45'le_452 (coe v0)) (d_stack'45'eq_458 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-mov-input2-to-output
d_sim'45'mov'45'input2'45'to'45'output_664 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 -> T_FlatCorr_368
d_sim'45'mov'45'input2'45'to'45'output_664 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'mov'45'input2'45'to'45'output_664 v5
du_sim'45'mov'45'input2'45'to'45'output_664 ::
  T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'mov'45'input2'45'to'45'output_664 v0
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v0))
      (d_dom'45'written_442 (coe v0)) (d_dom'45'sized_446 (coe v0))
      (d_lo'45'le_452 (coe v0)) (d_stack'45'eq_458 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-mov-output-to-input2
d_sim'45'mov'45'output'45'to'45'input2_680 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 -> T_FlatCorr_368
d_sim'45'mov'45'output'45'to'45'input2_680 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'mov'45'output'45'to'45'input2_680 v5
du_sim'45'mov'45'output'45'to'45'input2_680 ::
  T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'mov'45'output'45'to'45'input2_680 v0
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v0))
      (d_dom'45'written_442 (coe v0)) (d_dom'45'sized_446 (coe v0))
      (d_lo'45'le_452 (coe v0)) (d_stack'45'eq_458 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-tag-lit
d_sim'45'load'45'tag'45'lit_698 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 -> T_FlatCorr_368
d_sim'45'load'45'tag'45'lit_698 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_sim'45'load'45'tag'45'lit_698 v6
du_sim'45'load'45'tag'45'lit_698 ::
  T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'load'45'tag'45'lit_698 v0
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v0))
      (d_dom'45'written_442 (coe v0)) (d_dom'45'sized_446 (coe v0))
      (d_lo'45'le_452 (coe v0)) (d_stack'45'eq_458 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-reg-scratch-one
d_sim'45'reg'45'scratch'45'one_716 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 -> T_FlatCorr_368
d_sim'45'reg'45'scratch'45'one_716 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'reg'45'scratch'45'one_716 v5
du_sim'45'reg'45'scratch'45'one_716 ::
  T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'reg'45'scratch'45'one_716 v0
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v0))
      (d_dom'45'written_442 (coe v0)) (d_dom'45'sized_446 (coe v0))
      (d_lo'45'le_452 (coe v0)) (d_stack'45'eq_458 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-reg-scratch-zero
d_sim'45'reg'45'scratch'45'zero_732 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 -> T_FlatCorr_368
d_sim'45'reg'45'scratch'45'zero_732 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'reg'45'scratch'45'zero_732 v5
du_sim'45'reg'45'scratch'45'zero_732 ::
  T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'reg'45'scratch'45'zero_732 v0
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v0))
      (d_dom'45'written_442 (coe v0)) (d_dom'45'sized_446 (coe v0))
      (d_lo'45'le_452 (coe v0)) (d_stack'45'eq_458 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-reg-count-zero
d_sim'45'reg'45'count'45'zero_748 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 -> T_FlatCorr_368
d_sim'45'reg'45'count'45'zero_748 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'reg'45'count'45'zero_748 v5
du_sim'45'reg'45'count'45'zero_748 ::
  T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'reg'45'count'45'zero_748 v0
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v0))
      (d_dom'45'written_442 (coe v0)) (d_dom'45'sized_446 (coe v0))
      (d_lo'45'le_452 (coe v0)) (d_stack'45'eq_458 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-reg-scratch-load-count
d_sim'45'reg'45'scratch'45'load'45'count_764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 -> T_FlatCorr_368
d_sim'45'reg'45'scratch'45'load'45'count_764 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'reg'45'scratch'45'load'45'count_764 v5
du_sim'45'reg'45'scratch'45'load'45'count_764 ::
  T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'reg'45'scratch'45'load'45'count_764 v0
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v0))
      (d_dom'45'written_442 (coe v0)) (d_dom'45'sized_446 (coe v0))
      (d_lo'45'le_452 (coe v0)) (d_stack'45'eq_458 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sv-tag-zero
d_sv'45'tag'45'zero_776 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sv'45'tag'45'zero_776 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.enc-zero
d_enc'45'zero_784 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'zero_784 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-indirect-suc
d_sim'45'load'45'indirect'45'suc_798 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_368
d_sim'45'load'45'indirect'45'suc_798 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
                                     ~v8 ~v9
  = du_sim'45'load'45'indirect'45'suc_798 v7
du_sim'45'load'45'indirect'45'suc_798 ::
  T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'load'45'indirect'45'suc_798 v0
  = coe du_corr'45'clean_834 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_820 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_820 v0 ~v1 v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9
  = du_xpost_820 v0 v2 v4 v6
du_xpost_820 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_820 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v3))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
         (coe du_enc'45'sv_312 v0 v1 v2))
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
d_cleanFlat_822 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_cleanFlat_822 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_cleanFlat_822 v4 v5
du_cleanFlat_822 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_cleanFlat_822 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_84
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_168
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_82 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.floc-eq
d_floc'45'eq_824 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_824 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_830 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_830 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_834 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_368
d_corr'45'clean_834 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9
  = du_corr'45'clean_834 v7
du_corr'45'clean_834 :: T_FlatCorr_368 -> T_FlatCorr_368
du_corr'45'clean_834 v0
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v0))
      (d_dom'45'written_442 (coe v0)) (d_dom'45'sized_446 (coe v0))
      (d_lo'45'le_452 (coe v0)) (d_stack'45'eq_458 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-indirect
d_sim'45'load'45'indirect_848 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_368
d_sim'45'load'45'indirect_848 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
                              ~v9
  = du_sim'45'load'45'indirect_848 v7
du_sim'45'load'45'indirect_848 :: T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'load'45'indirect_848 v0
  = coe du_corr'45'clean_884 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_870 v0 ~v1 v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9
  = du_xpost_870 v0 v2 v4 v6
du_xpost_870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_870 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v3))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
         (coe du_enc'45'sv_312 v0 v1 v2))
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
d_cleanFlat_872 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_cleanFlat_872 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_cleanFlat_872 v4 v5
du_cleanFlat_872 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_cleanFlat_872 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_84
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_168
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_82 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.floc-eq
d_floc'45'eq_874 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_874 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_880 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_880 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_884 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_368
d_corr'45'clean_884 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9
  = du_corr'45'clean_884 v7
du_corr'45'clean_884 :: T_FlatCorr_368 -> T_FlatCorr_368
du_corr'45'clean_884 v0
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v0))
      (d_dom'45'written_442 (coe v0)) (d_dom'45'sized_446 (coe v0))
      (d_lo'45'le_452 (coe v0)) (d_stack'45'eq_458 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-from-slot
d_sim'45'load'45'from'45'slot_898 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_368
d_sim'45'load'45'from'45'slot_898 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
                                  ~v8
  = du_sim'45'load'45'from'45'slot_898 v7
du_sim'45'load'45'from'45'slot_898 ::
  T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'load'45'from'45'slot_898 v0
  = coe du_corr'45'clean_930 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_918 v0 ~v1 v2 ~v3 v4 ~v5 v6 ~v7 ~v8
  = du_xpost_918 v0 v2 v4 v6
du_xpost_918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_918 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v3))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
         (coe du_enc'45'sv_312 v0 v1 v2))
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
d_ex'45'eq_920 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ex'45'eq_920 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cleanFlat
d_cleanFlat_924 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_cleanFlat_924 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8
  = du_cleanFlat_924 v4 v5
du_cleanFlat_924 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_cleanFlat_924 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_84
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_168
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_82 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_926 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_926 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_930 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_368
d_corr'45'clean_930 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_corr'45'clean_930 v7
du_corr'45'clean_930 :: T_FlatCorr_368 -> T_FlatCorr_368
du_corr'45'clean_930 v0
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v0))
      (d_dom'45'written_442 (coe v0)) (d_dom'45'sized_446 (coe v0))
      (d_lo'45'le_452 (coe v0)) (d_stack'45'eq_458 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.≡ᵇ-refl
d_'8801''7495''45'refl_936 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_936 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.≢→≡ᵇfalse
d_'8802''8594''8801''7495'false_944 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8802''8594''8801''7495'false_944 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.untouched-write
d_untouched'45'write_968 ::
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
d_untouched'45'write_968 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.untouched-heap-store
d_untouched'45'heap'45'store_998 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny ->
  T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'heap'45'store_998 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.untouched-stack-store
d_untouched'45'stack'45'store_1036 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'stack'45'store_1036 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.store-heap-eq
d_store'45'heap'45'eq_1072 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'heap'45'eq_1072 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.store-dom-written
d_store'45'dom'45'written_1160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
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
d_store'45'dom'45'written_1160 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 v9
                               v10
  = du_store'45'dom'45'written_1160 v3 v6 v7 v8 v9 v10
du_store'45'dom'45'written_1160 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_store'45'dom'45'written_1160 v0 v1 v2 v3 v4 v5
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
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.read-write-miss
d_read'45'write'45'miss_1224 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'write'45'miss_1224 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.windows-reanchor
d_windows'45'reanchor_1256 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
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
d_windows'45'reanchor_1256 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           v10 v11
  = du_windows'45'reanchor_1256 v10 v11
du_windows'45'reanchor_1256 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'reanchor_1256 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             seq (coe v3)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.windows-leave
d_windows'45'leave_1284 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'leave_1284 v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7
  = du_windows'45'leave_1284 v0 v5 v7
du_windows'45'leave_1284 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'leave_1284 v0 v1 v2
  = coe
      du_go_1304 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
         (coe v1))
      (coe v2)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.go
d_go_1304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
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
d_go_1304 v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9 v10
  = du_go_1304 v0 v5 v8 v10
du_go_1304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_1304 v0 v1 v2 v3
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
d_windows'45'above_1350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
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
d_windows'45'above_1350 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
                        v11
  = du_windows'45'above_1350 v8 v11
du_windows'45'above_1350 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny -> AgdaAny
du_windows'45'above_1350 v0 v1
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
                                 (coe du_windows'45'above_1350 (coe v3) (coe v7)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.up
d_up_1400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
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
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_up_1400 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 v13
          ~v14 ~v15
  = du_up_1400 v0 v8 v13
du_up_1400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_up_1400 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v2)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0 v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.windows-write-below
d_windows'45'write'45'below_1428 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_windows'45'write'45'below_1428 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
                                 ~v9
  = du_windows'45'write'45'below_1428 v8
du_windows'45'write'45'below_1428 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny -> AgdaAny
du_windows'45'write'45'below_1428 v0
  = coe du_windows'45'above_1350 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.windows-heap-store
d_windows'45'heap'45'store_1470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny -> T_FlatCorr_368 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'heap'45'store_1470 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_windows'45'heap'45'store_1470 v3 v8
du_windows'45'heap'45'store_1470 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatCorr_368 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'heap'45'store_1470 v0 v1
  = coe
      du_windows'45'write'45'below_1428
      (coe
         du_frames'45'of_320
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0)))
      (d_stack'45'eq_458 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-store-indirect
d_sim'45'store'45'indirect_1494 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_368
d_sim'45'store'45'indirect_1494 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 ~v7 v8 ~v9
  = du_sim'45'store'45'indirect_1494 v3 v4 v6 v8
du_sim'45'store'45'indirect_1494 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatCorr_368 -> AgdaAny -> T_FlatCorr_368
du_sim'45'store'45'indirect_1494 v0 v1 v2 v3
  = coe du_corr'45'clean_1530 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.v
d_v_1516 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_v_1516 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_v_1516 v4
du_v_1516 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_v_1516 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_1518 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_1518 v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_xpost_1518 v0 v2 v3 v4 v5
du_xpost_1518 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_1518 v0 v1 v2 v3 v4
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
         (coe d_haddr_244 v1 v2)
         (coe du_enc'45'sv_312 v0 v1 (coe du_v_1516 (coe v3))))
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
d_cleanFlat_1520 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_cleanFlat_1520 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_cleanFlat_1520 v3 v4
du_cleanFlat_1520 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_cleanFlat_1520 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_84
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_784
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1))
         (coe v0) (coe du_v_1516 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_82 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.floc-eq
d_floc'45'eq_1522 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_1522 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_1526 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_1526 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_1530 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_368
d_corr'45'clean_1530 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 ~v7 v8 ~v9
  = du_corr'45'clean_1530 v3 v4 v6 v8
du_corr'45'clean_1530 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatCorr_368 -> AgdaAny -> T_FlatCorr_368
du_corr'45'clean_1530 v0 v1 v2 v3
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v2))
      (coe
         du_store'45'dom'45'written_1160 (coe v0) (coe v3)
         (coe d_dom'45'written_442 (coe v2)))
      (d_dom'45'sized_446 (coe v2)) (d_lo'45'le_452 (coe v2))
      (coe du_windows'45'heap'45'store_1470 (coe v1) (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-store-indirect-suc
d_sim'45'store'45'indirect'45'suc_1542 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_368
d_sim'45'store'45'indirect'45'suc_1542 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 ~v7
                                       v8 ~v9
  = du_sim'45'store'45'indirect'45'suc_1542 v3 v4 v6 v8
du_sim'45'store'45'indirect'45'suc_1542 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatCorr_368 -> AgdaAny -> T_FlatCorr_368
du_sim'45'store'45'indirect'45'suc_1542 v0 v1 v2 v3
  = coe du_corr'45'clean_1578 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.v
d_v_1564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_v_1564 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_v_1564 v4
du_v_1564 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_v_1564 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_1566 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_1566 v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_xpost_1566 v0 v2 v3 v4 v5
du_xpost_1566 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_1566 v0 v1 v2 v3 v4
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
            d_haddr_244 v1
            (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v2)))
         (coe du_enc'45'sv_312 v0 v1 (coe du_v_1564 (coe v3))))
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
d_cleanFlat_1568 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_cleanFlat_1568 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_cleanFlat_1568 v3 v4
du_cleanFlat_1568 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_cleanFlat_1568 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_84
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_784
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1))
         (coe MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v0))
         (coe du_v_1564 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_82 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.floc-eq
d_floc'45'eq_1570 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_1570 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_1574 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_1574 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_1578 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_368
d_corr'45'clean_1578 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 ~v7 v8 ~v9
  = du_corr'45'clean_1578 v3 v4 v6 v8
du_corr'45'clean_1578 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatCorr_368 -> AgdaAny -> T_FlatCorr_368
du_corr'45'clean_1578 v0 v1 v2 v3
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v2))
      (coe
         du_store'45'dom'45'written_1160
         (coe MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v0))
         (coe v3) (coe d_dom'45'written_442 (coe v2)))
      (d_dom'45'sized_446 (coe v2)) (d_lo'45'le_452 (coe v2))
      (coe du_windows'45'heap'45'store_1470 (coe v1) (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-restore-input
d_sim'45'restore'45'input_1592 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_368
d_sim'45'restore'45'input_1592 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_sim'45'restore'45'input_1592 v7
du_sim'45'restore'45'input_1592 :: T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'restore'45'input_1592 v0
  = coe du_corr'45'clean_1624 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_1612 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_1612 v0 ~v1 v2 ~v3 v4 ~v5 v6 ~v7 ~v8
  = du_xpost_1612 v0 v2 v4 v6
du_xpost_1612 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_1612 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v3))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20)
         (coe du_enc'45'sv_312 v0 v1 v2))
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
d_ex'45'eq_1614 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ex'45'eq_1614 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cleanFlat
d_cleanFlat_1618 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_cleanFlat_1618 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8
  = du_cleanFlat_1618 v4 v5
du_cleanFlat_1618 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_cleanFlat_1618 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_84
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_168
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_82 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_1620 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_1620 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_1624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_368
d_corr'45'clean_1624 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_corr'45'clean_1624 v7
du_corr'45'clean_1624 :: T_FlatCorr_368 -> T_FlatCorr_368
du_corr'45'clean_1624 v0
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v0))
      (d_dom'45'written_442 (coe v0)) (d_dom'45'sized_446 (coe v0))
      (d_lo'45'le_452 (coe v0)) (d_stack'45'eq_458 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.slot-addr-inj
d_slot'45'addr'45'inj_1634 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'inj_1634 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.atstack-slot-inj
d_atstack'45'slot'45'inj_1650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atstack'45'slot'45'inj_1650 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.atstack-frame-inj
d_atstack'45'frame'45'inj_1662 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atstack'45'frame'45'inj_1662 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.store-slot-heap-eq
d_store'45'slot'45'heap'45'eq_1680 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
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
d_store'45'slot'45'heap'45'eq_1680 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.store-slot-stack-eq
d_store'45'slot'45'stack'45'eq_1726 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  (Integer -> Maybe Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'slot'45'stack'45'eq_1726 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.go
d_go_1754 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  (Integer -> Maybe Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_1754 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.windows-slot-store
d_windows'45'slot'45'store_1796 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
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
d_windows'45'slot'45'store_1796 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                ~v9 v10 ~v11 v12
  = du_windows'45'slot'45'store_1796 v10 v12
du_windows'45'slot'45'store_1796 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'slot'45'store_1796 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                       (coe du_windows'45'above_1350 (coe v0) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.waddr
d_waddr_1828 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
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
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> Integer
d_waddr_1828 v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14
  = du_waddr_1828 v0 v5 v7
du_waddr_1828 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> Integer
du_waddr_1828 v0 v1 v2
  = coe
      addInt
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0 v1)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_slot'45'to'45'disp_10
         (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.mem'
d_mem''_1830 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
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
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> Integer -> Maybe Integer
d_mem''_1830 v0 ~v1 v2 v3 ~v4 v5 ~v6 v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
             ~v14
  = du_mem''_1830 v0 v2 v3 v5 v7 v8
du_mem''_1830 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  (Integer -> Maybe Integer) ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer -> Maybe Integer
du_mem''_1830 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeMem_188
      (coe v2) (coe du_waddr_1828 (coe v0) (coe v3) (coe v4))
      (coe du_enc'45'sv'45'at_276 (coe v0) (coe v1) (coe v5))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.w<fl
d_w'60'fl_1832 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
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
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_w'60'fl_1832 v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 ~v8 ~v9 ~v10 v11 ~v12
               ~v13 ~v14
  = du_w'60'fl_1832 v0 v5 v6 v7 v11
du_w'60'fl_1832 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_w'60'fl_1832 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3714
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0 v1)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'737''45''60'_4240
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80)
         (coe v3) (coe v2) (coe v4))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.base<
d_base'60'_1836 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
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
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_base'60'_1836 v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 ~v8 ~v9 ~v10 v11 ~v12
                ~v13 ~v14 v15 v16
  = du_base'60'_1836 v0 v5 v6 v7 v11 v15 v16
du_base'60'_1836 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_base'60'_1836 v0 v1 v2 v3 v4 v5 v6
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
d_sim'45'store'45'at'45'slot_1864 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FlatCorr_368
d_sim'45'store'45'at'45'slot_1864 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 ~v8
  = du_sim'45'store'45'at'45'slot_1864 v4 v6
du_sim'45'store'45'at'45'slot_1864 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'store'45'at'45'slot_1864 v0 v1
  = coe du_corr'45'clean_1892 (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.base
d_base_1884 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer
d_base_1884 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 = du_base_1884 v5
du_base_1884 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer
du_base_1884 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.Out
d_Out_1886 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_Out_1886 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 = du_Out_1886 v4
du_Out_1886 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_Out_1886 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cf
d_cf_1888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
d_cf_1888 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 = du_cf_1888 v4
du_cf_1888 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> AgdaAny
du_cf_1888 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_1890 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_1890 v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8
  = du_xpost_1890 v0 v2 v3 v4 v5
du_xpost_1890 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_1890 v0 v1 v2 v3 v4
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
            addInt (coe du_base_1884 (coe v4))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_slot'45'to'45'disp_10
               (coe v2)))
         (coe du_enc'45'sv_312 v0 v1 (coe du_Out_1886 (coe v3))))
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
d_corr'45'clean_1892 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FlatCorr_368
d_corr'45'clean_1892 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 ~v8
  = du_corr'45'clean_1892 v4 v6
du_corr'45'clean_1892 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatCorr_368 -> T_FlatCorr_368
du_corr'45'clean_1892 v0 v1
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v1))
      (d_dom'45'written_442 (coe v1)) (d_dom'45'sized_446 (coe v1))
      (d_lo'45'le_452 (coe v1))
      (coe
         du_windows'45'slot'45'store_1796
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0)))
         (coe d_stack'45'eq_458 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-alloc-stack
d_sim'45'alloc'45'stack_1916 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_FlatCorr_368
d_sim'45'alloc'45'stack_1916 v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7 ~v8 ~v9
                             ~v10 ~v11 ~v12 v13 ~v14
  = du_sim'45'alloc'45'stack_1916 v0 v3 v5 v7 v13
du_sim'45'alloc'45'stack_1916 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_FlatCorr_368
du_sim'45'alloc'45'stack_1916 v0 v1 v2 v3 v4
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v3))
      (d_dom'45'written_442 (coe v3)) (d_dom'45'sized_446 (coe v3)) v4
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
            (coe
               du_windows'45'reanchor_1256
               (coe du_tail'45'le_1964 (coe v0) (coe v1) (coe v2))
               (coe d_stack'45'eq_458 (coe v3)))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cf
d_cf_1948 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_cf_1948 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14
  = du_cf_1948 v5
du_cf_1948 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> AgdaAny
du_cf_1948 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.newbase
d_newbase_1950 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_newbase_1950 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.stk
d_stk_1958 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stk_1958 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.tail-le
d_tail'45'le_1964 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_tail'45'le_1964 v0 ~v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14
  = du_tail'45'le_1964 v0 v3 v5
du_tail'45'le_1964 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_tail'45'le_1964 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0
            (coe
               MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_102 v0
               (coe du_cf_1948 (coe v2)) v1))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_82 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-dealloc-stack
d_sim'45'dealloc'45'stack_1980 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_368
d_sim'45'dealloc'45'stack_1980 v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 ~v8
  = du_sim'45'dealloc'45'stack_1980 v0 v5 v6 v7
du_sim'45'dealloc'45'stack_1980 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'dealloc'45'stack_1980 v0 v1 v2 v3
  = coe
      C_constructor_460 (\ v4 v5 -> coe d_dom'45'fresh_436 v3 v4 v5)
      (d_dom'45'written_442 (coe v3))
      (\ v4 v5 -> coe d_dom'45'sized_446 v3 v4 v5)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe d_lo'45'le_452 (coe v3))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v2))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))))
      (coe
         du_windows'45'leave_1284 (coe v0)
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v1))
         (coe d_stack'45'eq_458 (coe v3)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-const
d_sim'45'load'45'const_2016 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 -> T_FlatCorr_368
d_sim'45'load'45'const_2016 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_sim'45'load'45'const_2016 v6
du_sim'45'load'45'const_2016 :: T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'load'45'const_2016 v0
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v0))
      (d_dom'45'written_442 (coe v0)) (d_dom'45'sized_446 (coe v0))
      (d_lo'45'le_452 (coe v0)) (d_stack'45'eq_458 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-const-float
d_sim'45'load'45'const'45'float_2036 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 -> T_FlatCorr_368
d_sim'45'load'45'const'45'float_2036 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_sim'45'load'45'const'45'float_2036 v6
du_sim'45'load'45'const'45'float_2036 ::
  T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'load'45'const'45'float_2036 v0
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v0))
      (d_dom'45'written_442 (coe v0)) (d_dom'45'sized_446 (coe v0))
      (d_lo'45'le_452 (coe v0)) (d_stack'45'eq_458 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-code-addr
d_sim'45'load'45'code'45'addr_2056 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 -> T_FlatCorr_368
d_sim'45'load'45'code'45'addr_2056 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_sim'45'load'45'code'45'addr_2056 v6
du_sim'45'load'45'code'45'addr_2056 ::
  T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'load'45'code'45'addr_2056 v0
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v0))
      (d_dom'45'written_442 (coe v0)) (d_dom'45'sized_446 (coe v0))
      (d_lo'45'le_452 (coe v0)) (d_stack'45'eq_458 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-save-closure-reg
d_sim'45'save'45'closure'45'reg_2074 ::
  T_FlatCorr_368 -> T_FlatCorr_368
d_sim'45'save'45'closure'45'reg_2074 v0 = coe v0
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.inc-enc
d_inc'45'enc_2090 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inc'45'enc_2090 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.dec-enc
d_dec'45'enc_2100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dec'45'enc_2100 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-reg-count-inc
d_sim'45'reg'45'count'45'inc_2114 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_368
d_sim'45'reg'45'count'45'inc_2114 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
                                  ~v8
  = du_sim'45'reg'45'count'45'inc_2114 v7
du_sim'45'reg'45'count'45'inc_2114 ::
  T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'reg'45'count'45'inc_2114 v0
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v0))
      (d_dom'45'written_442 (coe v0)) (d_dom'45'sized_446 (coe v0))
      (d_lo'45'le_452 (coe v0)) (d_stack'45'eq_458 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-reg-scratch-dec
d_sim'45'reg'45'scratch'45'dec_2142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_368
d_sim'45'reg'45'scratch'45'dec_2142 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
                                    ~v8
  = du_sim'45'reg'45'scratch'45'dec_2142 v7
du_sim'45'reg'45'scratch'45'dec_2142 ::
  T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'reg'45'scratch'45'dec_2142 v0
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v0))
      (d_dom'45'written_442 (coe v0)) (d_dom'45'sized_446 (coe v0))
      (d_lo'45'le_452 (coe v0)) (d_stack'45'eq_458 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ext-addr-aux
d_ext'45'addr'45'aux_2166 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
d_ext'45'addr'45'aux_2166 ~v0 ~v1 v2 v3 ~v4 v5
  = du_ext'45'addr'45'aux_2166 v2 v3 v5
du_ext'45'addr'45'aux_2166 ::
  T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
du_ext'45'addr'45'aux_2166 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    addInt (coe d_hfront_248 (coe v0))
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_slot'45'to'45'disp_10
                       (coe
                          MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50 (coe v1)))
             else coe seq (coe v4) (coe d_haddr_244 v0 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ext-addr
d_ext'45'addr_2184 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_ext'45'addr_2184 ~v0 ~v1 v2 v3 v4 = du_ext'45'addr_2184 v2 v3 v4
du_ext'45'addr_2184 ::
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
du_ext'45'addr_2184 v0 v1 v2
  = coe
      du_ext'45'addr'45'aux_2166 (coe v0) (coe v2)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48 (coe v2)))
         (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ExtDom
d_ExtDom_2200 a0 a1 a2 a3 a4 a5 = ()
data T_ExtDom_2200
  = C_ext'45'old_2210 AgdaAny |
    C_ext'45'fresh_2212 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ext-addr-old
d_ext'45'addr'45'old_2220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'old_2220 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.go
d_go_2236 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_2236 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ext-addr-fresh
d_ext'45'addr'45'fresh_2246 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'fresh_2246 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.go
d_go_2262 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_2262 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ext-addr-base
d_ext'45'addr'45'base_2270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'base_2270 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.+-not-<
d_'43''45'not'45''60'_2280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'43''45'not'45''60'_2280 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ext-suc-aux
d_ext'45'suc'45'aux_2298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'suc'45'aux_2298 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ext-suc
d_ext'45'suc_2324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'suc_2324 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.extend-view
d_extend'45'view_2342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_HeapView_218
d_extend'45'view_2342 ~v0 ~v1 v2 v3 v4 ~v5 v6
  = du_extend'45'view_2342 v2 v3 v4 v6
du_extend'45'view_2342 ::
  T_HeapView_218 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_HeapView_218
du_extend'45'view_2342 v0 v1 v2 v3
  = coe
      C_mkHV_268 (coe du_ext'45'addr_2184 (coe v0) (coe v1))
      (addInt
         (coe d_hfront_248 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_82 (coe v2)))
      (coe du_below_2360 (coe v0) (coe v2)) (d_lo_264 (coe v0)) v3
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.below
d_below_2360 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_2200 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_below_2360 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 v7 v8
  = du_below_2360 v2 v4 v7 v8
du_below_2360 ::
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_2200 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_below_2360 v0 v1 v2 v3
  = case coe v3 of
      C_ext'45'old_2210 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'60''45'trans'737'_6714
             (coe d_haddr_244 v0 v2) (d_hfront_248 (coe v0))
             (addInt
                (coe d_hfront_248 (coe v0))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_82 (coe v1)))
             (coe d_dom'45'below_262 v0 v2 v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                (coe d_hfront_248 (coe v0)))
      C_ext'45'fresh_2212 v5
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3714
             (coe d_hfront_248 (coe v0))
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'737''45''60'_4240
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80)
                (coe
                   MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50 (coe v2))
                (coe v1) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cross
d_cross_2380 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
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
d_cross_2380 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.inj
d_inj_2398 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_2200 ->
  T_ExtDom_2200 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inj_2398 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._._.addr-eq
d_addr'45'eq_2448 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
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
d_addr'45'eq_2448 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._._.off-eq
d_off'45'eq_2450 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
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
d_off'45'eq_2450 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.enc-ext
d_enc'45'ext_2466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'ext_2466 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.enc-ext-maybe
d_enc'45'ext'45'maybe_2550 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'ext'45'maybe_2550 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.windows-enc-ext
d_windows'45'enc'45'ext_2600 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
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
d_windows'45'enc'45'ext_2600 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                             ~v9 v10 ~v11 v12
  = du_windows'45'enc'45'ext_2600 v10 v12
du_windows'45'enc'45'ext_2600 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny -> AgdaAny
du_windows'45'enc'45'ext_2600 v0 v1
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
                                 (coe du_windows'45'enc'45'ext_2600 (coe v3) (coe v7)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-alloc-heap
d_sim'45'alloc'45'heap_2680 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
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
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_FlatCorr_368
d_sim'45'alloc'45'heap_2680 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9
                            ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16
  = du_sim'45'alloc'45'heap_2680 v6 v8
du_sim'45'alloc'45'heap_2680 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'alloc'45'heap_2680 v0 v1
  = coe
      C_constructor_460 (coe du_df_2754 (coe v0) (coe v1))
      (\ v2 v3 v4 ->
         coe C_ext'45'old_2210 (coe d_dom'45'written_442 v1 v2 v3 erased))
      (coe du_ds_2722 (coe v0) (coe v1)) (d_lo'45'le_452 (coe v1))
      (coe
         du_windows'45'enc'45'ext_2600
         (coe
            du_frames'45'of_320
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0)))
         (coe d_stack'45'eq_458 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.st
d_st_2716 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
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
d_st_2716 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16
  = du_st_2716 v6
du_st_2716 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> Integer
du_st_2716 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.dfr
d_dfr_2718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
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
d_dfr_2718 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16
  = du_dfr_2718 v8
du_dfr_2718 ::
  T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_dfr_2718 v0 = coe d_dom'45'fresh_436 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.ds
d_ds_2722 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
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
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_ExtDom_2200
d_ds_2722 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 v17 v18
  = du_ds_2722 v6 v8 v17 v18
du_ds_2722 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_ExtDom_2200
du_ds_2722 v0 v1 v2 v3
  = coe
      du_go_2734 (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48 (coe v2)))
         (coe du_st_2716 (coe v0)))
      (coe v3)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._._.go
d_go_2734 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
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
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_ExtDom_2200
d_go_2734 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 v17 ~v18 v19 v20
  = du_go_2734 v8 v17 v19 v20
du_go_2734 ::
  T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_ExtDom_2200
du_go_2734 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe seq (coe v5) (coe C_ext'45'fresh_2212 v3)
             else coe
                    seq (coe v5)
                    (coe C_ext'45'old_2210 (coe d_dom'45'sized_446 v0 v1 v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.hv'
d_hv''_2742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
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
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_HeapView_218
d_hv''_2742 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 v16
  = du_hv''_2742 v2 v3 v6 v16
du_hv''_2742 ::
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_HeapView_218
du_hv''_2742 v0 v1 v2 v3
  = coe
      du_extend'45'view_2342 (coe v0) (coe du_st_2716 (coe v2)) (coe v1)
      (coe v3)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.fresh-x86
d_fresh'45'x86_2746 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
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
d_fresh'45'x86_2746 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.df
d_df_2754 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
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
  T_ExtDom_2200 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_df_2754 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 v17 v18
  = du_df_2754 v6 v8 v17 v18
du_df_2754 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_2200 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_df_2754 v0 v1 v2 v3
  = case coe v3 of
      C_ext'45'old_2210 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_m'60'n'8658'm'60'1'43'n_3204
             (coe du_dfr_2718 v1 v2 v4)
      C_ext'45'fresh_2212 v5
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe addInt (coe (1 :: Integer)) (coe du_st_2716 (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.hp
d_hp_2764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
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
  T_ExtDom_2200 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hp_2764 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-lea-slot
d_sim'45'lea'45'slot_2796 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 -> T_FlatCorr_368
d_sim'45'lea'45'slot_2796 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_sim'45'lea'45'slot_2796 v6
du_sim'45'lea'45'slot_2796 :: T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'lea'45'slot_2796 v0
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v0))
      (d_dom'45'written_442 (coe v0)) (d_dom'45'sized_446 (coe v0))
      (d_lo'45'le_452 (coe v0)) (d_stack'45'eq_458 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cf
d_cf_2812 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 -> AgdaAny
d_cf_2812 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du_cf_2812 v4
du_cf_2812 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> AgdaAny
du_cf_2812 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.addr-eq
d_addr'45'eq_2814 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_addr'45'eq_2814 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-indirect-stack
d_sim'45'load'45'indirect'45'stack_2832 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_368
d_sim'45'load'45'indirect'45'stack_2832 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 v8 ~v9 ~v10
  = du_sim'45'load'45'indirect'45'stack_2832 v8
du_sim'45'load'45'indirect'45'stack_2832 ::
  T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'load'45'indirect'45'stack_2832 v0
  = coe du_corr'45'clean_2870 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_2856 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_2856 v0 ~v1 v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10
  = du_xpost_2856 v0 v2 v5 v7
du_xpost_2856 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_2856 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v3))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
         (coe du_enc'45'sv_312 v0 v1 v2))
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
d_cleanFlat_2858 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_cleanFlat_2858 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_cleanFlat_2858 v5 v6
du_cleanFlat_2858 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_cleanFlat_2858 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_84
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_168
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_82 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.floc-eq
d_floc'45'eq_2860 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_2860 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_2866 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_2866 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_2870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_368
d_corr'45'clean_2870 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_corr'45'clean_2870 v8
du_corr'45'clean_2870 :: T_FlatCorr_368 -> T_FlatCorr_368
du_corr'45'clean_2870 v0
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v0))
      (d_dom'45'written_442 (coe v0)) (d_dom'45'sized_446 (coe v0))
      (d_lo'45'le_452 (coe v0)) (d_stack'45'eq_458 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-indirect-suc-stack
d_sim'45'load'45'indirect'45'suc'45'stack_2886 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_368
d_sim'45'load'45'indirect'45'suc'45'stack_2886 ~v0 ~v1 ~v2 ~v3 ~v4
                                               ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_sim'45'load'45'indirect'45'suc'45'stack_2886 v8
du_sim'45'load'45'indirect'45'suc'45'stack_2886 ::
  T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'load'45'indirect'45'suc'45'stack_2886 v0
  = coe du_corr'45'clean_2924 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_2910 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_2910 v0 ~v1 v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10
  = du_xpost_2910 v0 v2 v5 v7
du_xpost_2910 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_2910 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v3))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
         (coe du_enc'45'sv_312 v0 v1 v2))
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
d_cleanFlat_2912 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_cleanFlat_2912 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_cleanFlat_2912 v5 v6
du_cleanFlat_2912 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_cleanFlat_2912 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_84
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_168
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_82 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.floc-eq
d_floc'45'eq_2914 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_2914 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_2920 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_2920 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_2924 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_368
d_corr'45'clean_2924 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_corr'45'clean_2924 v8
du_corr'45'clean_2924 :: T_FlatCorr_368 -> T_FlatCorr_368
du_corr'45'clean_2924 v0
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v0))
      (d_dom'45'written_442 (coe v0)) (d_dom'45'sized_446 (coe v0))
      (d_lo'45'le_452 (coe v0)) (d_stack'45'eq_458 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-store-indirect-stack
d_sim'45'store'45'indirect'45'stack_2938 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FlatCorr_368
d_sim'45'store'45'indirect'45'stack_2938 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
                                         ~v7 ~v8 ~v9
  = du_sim'45'store'45'indirect'45'stack_2938 v4 v6
du_sim'45'store'45'indirect'45'stack_2938 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'store'45'indirect'45'stack_2938 v0 v1
  = coe du_corr'45'clean_2978 (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.base
d_base_2960 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer
d_base_2960 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_base_2960 v5
du_base_2960 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer
du_base_2960 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.Out
d_Out_2962 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_Out_2962 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_Out_2962 v4
du_Out_2962 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_Out_2962 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cf
d_cf_2964 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
d_cf_2964 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_cf_2964 v4
du_cf_2964 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> AgdaAny
du_cf_2964 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_2966 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_2966 v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_xpost_2966 v0 v2 v3 v4 v5
du_xpost_2966 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_2966 v0 v1 v2 v3 v4
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
            addInt (coe du_base_2960 (coe v4))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_slot'45'to'45'disp_10
               (coe v2)))
         (coe du_enc'45'sv_312 v0 v1 (coe du_Out_2962 (coe v3))))
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
d_cleanFlat_2968 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_cleanFlat_2968 v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_cleanFlat_2968 v0 v3 v4
du_cleanFlat_2968 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_cleanFlat_2968 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_84
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLocToStack_774 (coe v0)
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v2))
         (coe du_cf_2964 (coe v2)) (coe v1) (coe du_Out_2962 (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v2))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v2))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_82 (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.floc-eq
d_floc'45'eq_2970 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_2970 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_2974 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_2974 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_2978 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FlatCorr_368
d_corr'45'clean_2978 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9
  = du_corr'45'clean_2978 v4 v6
du_corr'45'clean_2978 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatCorr_368 -> T_FlatCorr_368
du_corr'45'clean_2978 v0 v1
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v1))
      (d_dom'45'written_442 (coe v1)) (d_dom'45'sized_446 (coe v1))
      (d_lo'45'le_452 (coe v1))
      (coe
         du_windows'45'slot'45'store_1796
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0)))
         (coe d_stack'45'eq_458 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-store-indirect-suc-stack
d_sim'45'store'45'indirect'45'suc'45'stack_2994 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FlatCorr_368
d_sim'45'store'45'indirect'45'suc'45'stack_2994 ~v0 ~v1 ~v2 ~v3 v4
                                                ~v5 v6 ~v7 ~v8 ~v9
  = du_sim'45'store'45'indirect'45'suc'45'stack_2994 v4 v6
du_sim'45'store'45'indirect'45'suc'45'stack_2994 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatCorr_368 -> T_FlatCorr_368
du_sim'45'store'45'indirect'45'suc'45'stack_2994 v0 v1
  = coe du_corr'45'clean_3034 (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.base
d_base_3016 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer
d_base_3016 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_base_3016 v5
du_base_3016 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer
du_base_3016 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.Out
d_Out_3018 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_Out_3018 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_Out_3018 v4
du_Out_3018 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_Out_3018 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cf
d_cf_3020 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
d_cf_3020 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_cf_3020 v4
du_cf_3020 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> AgdaAny
du_cf_3020 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_3022 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_3022 v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_xpost_3022 v0 v2 v3 v4 v5
du_xpost_3022 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_3022 v0 v1 v2 v3 v4
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
            addInt (coe du_base_3016 (coe v4))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_slot'45'to'45'disp_10
               (coe addInt (coe (1 :: Integer)) (coe v2))))
         (coe du_enc'45'sv_312 v0 v1 (coe du_Out_3018 (coe v3))))
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
d_cleanFlat_3024 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_cleanFlat_3024 v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_cleanFlat_3024 v0 v3 v4
du_cleanFlat_3024 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_cleanFlat_3024 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_84
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLocToStack_774 (coe v0)
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v2))
         (coe du_cf_3020 (coe v2))
         (coe addInt (coe (1 :: Integer)) (coe v1))
         (coe du_Out_3018 (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v2))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v2))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_82 (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.floc-eq
d_floc'45'eq_3026 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_3026 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_3030 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_3030 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_3034 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FlatCorr_368
d_corr'45'clean_3034 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9
  = du_corr'45'clean_3034 v4 v6
du_corr'45'clean_3034 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatCorr_368 -> T_FlatCorr_368
du_corr'45'clean_3034 v0 v1
  = coe
      C_constructor_460 (d_dom'45'fresh_436 (coe v1))
      (d_dom'45'written_442 (coe v1)) (d_dom'45'sized_446 (coe v1))
      (d_lo'45'le_452 (coe v1))
      (coe
         du_windows'45'slot'45'store_1796
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0)))
         (coe d_stack'45'eq_458 (coe v1)))
