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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.readLoc
d_readLoc_16 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_16 ~v0 ~v1 = du_readLoc_16
du_readLoc_16 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_16
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_646
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.writeHeapMem
d_writeHeapMem_18 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_writeHeapMem_18 ~v0 ~v1 = du_writeHeapMem_18
du_writeHeapMem_18 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_writeHeapMem_18
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem_698
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.writeLoc
d_writeLoc_20 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_writeLoc_20 v0 ~v1 = du_writeLoc_20 v0
du_writeLoc_20 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
du_writeLoc_20 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_726 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.writeLocToHeap
d_writeLocToHeap_26 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_writeLocToHeap_26 ~v0 ~v1 = du_writeLocToHeap_26
du_writeLocToHeap_26 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
du_writeLocToHeap_26
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_718
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_32 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_exec'45'load'45'suc'45'via'45'resolved_32 ~v0 ~v1
  = du_exec'45'load'45'suc'45'via'45'resolved_32
du_exec'45'load'45'suc'45'via'45'resolved_32 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
du_exec'45'load'45'suc'45'via'45'resolved_32
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'suc'45'via'45'resolved_1370
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_34 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_exec'45'load'45'via'45'resolved_34 ~v0 ~v1
  = du_exec'45'load'45'via'45'resolved_34
du_exec'45'load'45'via'45'resolved_34 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
du_exec'45'load'45'via'45'resolved_34
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'via'45'resolved_1332
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_38 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_exec'45'store'45'suc'45'via'45'resolved_38 v0 ~v1
  = du_exec'45'store'45'suc'45'via'45'resolved_38 v0
du_exec'45'store'45'suc'45'via'45'resolved_38 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
du_exec'45'store'45'suc'45'via'45'resolved_38 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'suc'45'via'45'resolved_1382
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_40 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_exec'45'store'45'via'45'resolved_40 v0 ~v1
  = du_exec'45'store'45'via'45'resolved_40 v0
du_exec'45'store'45'via'45'resolved_40 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
du_exec'45'store'45'via'45'resolved_40 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'via'45'resolved_1344
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatState
d_FlatState_46 a0 a1 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.flat-exec-instr
d_flat'45'exec'45'instr_92 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_flat'45'exec'45'instr_92 v0 ~v1 = du_flat'45'exec'45'instr_92 v0
du_flat'45'exec'45'instr_92 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_flat'45'exec'45'instr_92 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_244
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.leave-frame
d_leave'45'frame_110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510
d_leave'45'frame_110 ~v0 ~v1 = du_leave'45'frame_110
du_leave'45'frame_110 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510
du_leave'45'frame_110
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame_196
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sv-is-zero
d_sv'45'is'45'zero_124 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_sv'45'is'45'zero_124 ~v0 ~v1 = du_sv'45'is'45'zero_124
du_sv'45'is'45'zero_124 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_sv'45'is'45'zero_124
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_78
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatState.falloc
d_falloc_130 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510
d_falloc_130 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatState.floc
d_floc_132 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_floc_132 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatState.fpc
d_fpc_134 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> Integer
d_fpc_134 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_74 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.shift-frame
d_shift'45'frame_138 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> Integer -> AgdaAny
d_shift'45'frame_138 v0 ~v1 = du_shift'45'frame_138 v0
du_shift'45'frame_138 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> AgdaAny
du_shift'45'frame_138 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_102 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sv-below
d_sv'45'below_142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_sv'45'below_142 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.svm-below
d_svm'45'below_144 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_svm'45'below_144 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.exec-abstract
d_exec'45'abstract_148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_148 v0 ~v1 = du_exec'45'abstract_148 v0
du_exec'45'abstract_148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'abstract_148 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2584
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.Frame
d_Frame_156 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> ()
d_Frame_156 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.frame-base
d_frame'45'base_158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> Integer
d_frame'45'base_158 v0 ~v1 = du_frame'45'base_158 v0
du_frame'45'base_158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer
du_frame'45'base_158 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.slot-addr
d_slot'45'addr_164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> Integer -> Integer
d_slot'45'addr_164 v0 ~v1 = du_slot'45'addr_164 v0
du_slot'45'addr_164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> Integer
du_slot'45'addr_164 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_slot'45'addr_88 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView
d_HeapView_168 a0 a1 = ()
data T_HeapView_168
  = C_mkHV_210 (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                Integer)
               Integer
               (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView.haddr
d_haddr_190 ::
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_haddr_190 v0
  = case coe v0 of
      C_mkHV_210 v1 v3 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView.HDom
d_HDom_192 ::
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> ()
d_HDom_192 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView.hfront
d_hfront_194 :: T_HeapView_168 -> Integer
d_hfront_194 v0
  = case coe v0 of
      C_mkHV_210 v1 v3 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView.haddr-suc
d_haddr'45'suc_198 ::
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_198 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView.haddr-inj
d_haddr'45'inj_204 ::
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_204 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.HeapView.dom-below
d_dom'45'below_208 ::
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_208 v0
  = case coe v0 of
      C_mkHV_210 v1 v3 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.lit-word
d_lit'45'word_212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer
d_lit'45'word_212 ~v0 ~v1 v2 = du_lit'45'word_212 v2
du_lit'45'word_212 :: Integer -> Integer
du_lit'45'word_212 v0 = coe v0
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.enc-sv
d_enc'45'sv_216 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Integer
d_enc'45'sv_216 v0 ~v1 v2 v3 = du_enc'45'sv_216 v0 v2 v3
du_enc'45'sv_216 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Integer
du_enc'45'sv_216 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v3
        -> case coe v3 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
               -> coe
                    MAlonzo.Code.Once.CCC.FrameSemantics.d_slot'45'addr_88 v0 v4 v5
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
               -> coe d_haddr_190 v1 v4
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v3 -> coe v3
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C_fits'45'int_198 -> coe v5
             MAlonzo.Code.Once.Type.C_fits'45'float_200 -> coe (0 :: Integer)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.enc-maybe
d_enc'45'maybe_244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
d_enc'45'maybe_244 v0 ~v1 v2 v3 = du_enc'45'maybe_244 v0 v2 v3
du_enc'45'maybe_244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_168 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
du_enc'45'maybe_244 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe du_enc'45'sv_216 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr
d_FlatCorr_258 a0 a1 a2 a3 a4 = ()
newtype T_FlatCorr_258
  = C_constructor_318 (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                       AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.rdi-eq
d_rdi'45'eq_292 ::
  T_FlatCorr_258 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45'eq_292 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.rsi-eq
d_rsi'45'eq_294 ::
  T_FlatCorr_258 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rsi'45'eq_294 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.rax-eq
d_rax'45'eq_296 ::
  T_FlatCorr_258 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rax'45'eq_296 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.rbx-eq
d_rbx'45'eq_298 ::
  T_FlatCorr_258 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rbx'45'eq_298 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.halt-eq
d_halt'45'eq_300 ::
  T_FlatCorr_258 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45'eq_300 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.rsp-eq
d_rsp'45'eq_302 ::
  T_FlatCorr_258 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rsp'45'eq_302 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.r15-eq
d_r15'45'eq_304 ::
  T_FlatCorr_258 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r15'45'eq_304 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.dom-fresh
d_dom'45'fresh_308 ::
  T_FlatCorr_258 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'fresh_308 v0
  = case coe v0 of
      C_constructor_318 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.heap-eq
d_heap'45'eq_312 ::
  T_FlatCorr_258 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'eq_312 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.FlatCorr.stack-eq
d_stack'45'eq_316 ::
  T_FlatCorr_258 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'eq_316 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-mov-to-output
d_sim'45'mov'45'to'45'output_326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 -> T_FlatCorr_258
d_sim'45'mov'45'to'45'output_326 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'mov'45'to'45'output_326 v5
du_sim'45'mov'45'to'45'output_326 ::
  T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'mov'45'to'45'output_326 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-mov-to-input
d_sim'45'mov'45'to'45'input_342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 -> T_FlatCorr_258
d_sim'45'mov'45'to'45'input_342 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'mov'45'to'45'input_342 v5
du_sim'45'mov'45'to'45'input_342 ::
  T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'mov'45'to'45'input_342 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-mov-input2-to-output
d_sim'45'mov'45'input2'45'to'45'output_358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 -> T_FlatCorr_258
d_sim'45'mov'45'input2'45'to'45'output_358 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'mov'45'input2'45'to'45'output_358 v5
du_sim'45'mov'45'input2'45'to'45'output_358 ::
  T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'mov'45'input2'45'to'45'output_358 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-mov-output-to-input2
d_sim'45'mov'45'output'45'to'45'input2_374 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 -> T_FlatCorr_258
d_sim'45'mov'45'output'45'to'45'input2_374 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'mov'45'output'45'to'45'input2_374 v5
du_sim'45'mov'45'output'45'to'45'input2_374 ::
  T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'mov'45'output'45'to'45'input2_374 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-tag-lit
d_sim'45'load'45'tag'45'lit_392 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 -> T_FlatCorr_258
d_sim'45'load'45'tag'45'lit_392 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_sim'45'load'45'tag'45'lit_392 v6
du_sim'45'load'45'tag'45'lit_392 ::
  T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'load'45'tag'45'lit_392 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-reg-scratch-one
d_sim'45'reg'45'scratch'45'one_410 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 -> T_FlatCorr_258
d_sim'45'reg'45'scratch'45'one_410 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'reg'45'scratch'45'one_410 v5
du_sim'45'reg'45'scratch'45'one_410 ::
  T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'reg'45'scratch'45'one_410 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-reg-scratch-zero
d_sim'45'reg'45'scratch'45'zero_426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 -> T_FlatCorr_258
d_sim'45'reg'45'scratch'45'zero_426 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'reg'45'scratch'45'zero_426 v5
du_sim'45'reg'45'scratch'45'zero_426 ::
  T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'reg'45'scratch'45'zero_426 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-reg-input2-zero
d_sim'45'reg'45'input2'45'zero_442 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 -> T_FlatCorr_258
d_sim'45'reg'45'input2'45'zero_442 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'reg'45'input2'45'zero_442 v5
du_sim'45'reg'45'input2'45'zero_442 ::
  T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'reg'45'input2'45'zero_442 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-reg-scratch-load-count
d_sim'45'reg'45'scratch'45'load'45'count_458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 -> T_FlatCorr_258
d_sim'45'reg'45'scratch'45'load'45'count_458 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_sim'45'reg'45'scratch'45'load'45'count_458 v5
du_sim'45'reg'45'scratch'45'load'45'count_458 ::
  T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'reg'45'scratch'45'load'45'count_458 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sv-tag-zero
d_sv'45'tag'45'zero_470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sv'45'tag'45'zero_470 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.enc-zero
d_enc'45'zero_478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'zero_478 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-indirect-suc
d_sim'45'load'45'indirect'45'suc_492 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_258
d_sim'45'load'45'indirect'45'suc_492 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
                                     ~v8 ~v9
  = du_sim'45'load'45'indirect'45'suc_492 v7
du_sim'45'load'45'indirect'45'suc_492 ::
  T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'load'45'indirect'45'suc_492 v0
  = coe du_corr'45'clean_528 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_514 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_514 v0 ~v1 v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9
  = du_xpost_514 v0 v2 v4 v6
du_xpost_514 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_514 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v3))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
         (coe du_enc'45'sv_216 (coe v0) (coe v1) (coe v2)))
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
d_cleanFlat_516 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_cleanFlat_516 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_cleanFlat_516 v4 v5
du_cleanFlat_516 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_cleanFlat_516 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlat_76
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_476
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_164
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_470
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_472
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_474
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_74 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.floc-eq
d_floc'45'eq_518 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_518 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_524 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_524 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_258
d_corr'45'clean_528 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9
  = du_corr'45'clean_528 v7
du_corr'45'clean_528 :: T_FlatCorr_258 -> T_FlatCorr_258
du_corr'45'clean_528 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-indirect
d_sim'45'load'45'indirect_542 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_258
d_sim'45'load'45'indirect_542 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
                              ~v9
  = du_sim'45'load'45'indirect_542 v7
du_sim'45'load'45'indirect_542 :: T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'load'45'indirect_542 v0
  = coe du_corr'45'clean_578 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_564 v0 ~v1 v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9
  = du_xpost_564 v0 v2 v4 v6
du_xpost_564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_564 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v3))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
         (coe du_enc'45'sv_216 (coe v0) (coe v1) (coe v2)))
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
d_cleanFlat_566 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_cleanFlat_566 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_cleanFlat_566 v4 v5
du_cleanFlat_566 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_cleanFlat_566 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlat_76
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_476
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_164
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_470
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_472
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_474
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_74 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.floc-eq
d_floc'45'eq_568 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_568 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_574 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_574 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_578 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_258
d_corr'45'clean_578 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9
  = du_corr'45'clean_578 v7
du_corr'45'clean_578 :: T_FlatCorr_258 -> T_FlatCorr_258
du_corr'45'clean_578 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-from-slot
d_sim'45'load'45'from'45'slot_592 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_258
d_sim'45'load'45'from'45'slot_592 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
                                  ~v8
  = du_sim'45'load'45'from'45'slot_592 v7
du_sim'45'load'45'from'45'slot_592 ::
  T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'load'45'from'45'slot_592 v0
  = coe du_corr'45'clean_624 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_612 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_612 v0 ~v1 v2 ~v3 v4 ~v5 v6 ~v7 ~v8
  = du_xpost_612 v0 v2 v4 v6
du_xpost_612 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_612 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v3))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
         (coe du_enc'45'sv_216 (coe v0) (coe v1) (coe v2)))
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
d_ex'45'eq_614 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ex'45'eq_614 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cleanFlat
d_cleanFlat_618 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_cleanFlat_618 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8
  = du_cleanFlat_618 v4 v5
du_cleanFlat_618 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_cleanFlat_618 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlat_76
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_476
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_164
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_470
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_472
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_474
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_74 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_620 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_620 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_258
d_corr'45'clean_624 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_corr'45'clean_624 v7
du_corr'45'clean_624 :: T_FlatCorr_258 -> T_FlatCorr_258
du_corr'45'clean_624 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.≡ᵇ-refl
d_'8801''7495''45'refl_630 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_630 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.≢→≡ᵇfalse
d_'8802''8594''8801''7495'false_638 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8802''8594''8801''7495'false_638 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.store-heap-eq
d_store'45'heap'45'eq_668 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'heap'45'eq_668 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.store-stack-eq
d_store'45'stack'45'eq_758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  (Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'stack'45'eq_758 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-store-indirect
d_sim'45'store'45'indirect_794 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FlatCorr_258
d_sim'45'store'45'indirect_794 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8
                               ~v9 ~v10
  = du_sim'45'store'45'indirect_794 v6
du_sim'45'store'45'indirect_794 :: T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'store'45'indirect_794 v0
  = coe du_corr'45'clean_832 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.v
d_v_818 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_v_818 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 = du_v_818 v4
du_v_818 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_v_818 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_152
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_820 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_820 v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_xpost_820 v0 v2 v3 v4 v5
du_xpost_820 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_820 v0 v1 v2 v3 v4
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
         (coe d_haddr_190 v1 v2)
         (coe du_enc'45'sv_216 (coe v0) (coe v1) (coe du_v_818 (coe v3))))
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
d_cleanFlat_822 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_cleanFlat_822 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_cleanFlat_822 v3 v4
du_cleanFlat_822 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_cleanFlat_822 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlat_76
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_718
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v1))
         (coe v0) (coe du_v_818 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_74 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.floc-eq
d_floc'45'eq_824 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_824 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_828 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_828 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_832 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FlatCorr_258
d_corr'45'clean_832 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_corr'45'clean_832 v6
du_corr'45'clean_832 :: T_FlatCorr_258 -> T_FlatCorr_258
du_corr'45'clean_832 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-store-indirect-suc
d_sim'45'store'45'indirect'45'suc_846 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FlatCorr_258
d_sim'45'store'45'indirect'45'suc_846 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
                                      ~v7 ~v8 ~v9 ~v10
  = du_sim'45'store'45'indirect'45'suc_846 v6
du_sim'45'store'45'indirect'45'suc_846 ::
  T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'store'45'indirect'45'suc_846 v0
  = coe du_corr'45'clean_884 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.v
d_v_870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_v_870 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 = du_v_870 v4
du_v_870 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_v_870 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_152
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_872 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_872 v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_xpost_872 v0 v2 v3 v4 v5
du_xpost_872 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_872 v0 v1 v2 v3 v4
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
            d_haddr_190 v1
            (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v2)))
         (coe du_enc'45'sv_216 (coe v0) (coe v1) (coe du_v_870 (coe v3))))
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
d_cleanFlat_874 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_cleanFlat_874 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_cleanFlat_874 v3 v4
du_cleanFlat_874 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_cleanFlat_874 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlat_76
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_718
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v1))
         (coe MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v0))
         (coe du_v_870 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_74 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.floc-eq
d_floc'45'eq_876 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_876 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_880 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_880 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_884 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FlatCorr_258
d_corr'45'clean_884 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_corr'45'clean_884 v6
du_corr'45'clean_884 :: T_FlatCorr_258 -> T_FlatCorr_258
du_corr'45'clean_884 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-restore-input
d_sim'45'restore'45'input_898 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_258
d_sim'45'restore'45'input_898 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_sim'45'restore'45'input_898 v7
du_sim'45'restore'45'input_898 :: T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'restore'45'input_898 v0
  = coe du_corr'45'clean_930 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_918 v0 ~v1 v2 ~v3 v4 ~v5 v6 ~v7 ~v8
  = du_xpost_918 v0 v2 v4 v6
du_xpost_918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_918 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v3))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20)
         (coe du_enc'45'sv_216 (coe v0) (coe v1) (coe v2)))
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
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ex'45'eq_920 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cleanFlat
d_cleanFlat_924 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_cleanFlat_924 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8
  = du_cleanFlat_924 v4 v5
du_cleanFlat_924 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_cleanFlat_924 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlat_76
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_476
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_164
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_470
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_472
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_474
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_74 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_926 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_926 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_930 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_258
d_corr'45'clean_930 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_corr'45'clean_930 v7
du_corr'45'clean_930 :: T_FlatCorr_258 -> T_FlatCorr_258
du_corr'45'clean_930 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.slot-addr-inj
d_slot'45'addr'45'inj_940 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'inj_940 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.atstack-slot-inj
d_atstack'45'slot'45'inj_956 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atstack'45'slot'45'inj_956 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.store-slot-heap-eq
d_store'45'slot'45'heap'45'eq_976 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'slot'45'heap'45'eq_976 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.store-slot-stack-eq
d_store'45'slot'45'stack'45'eq_1022 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  AgdaAny ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'slot'45'stack'45'eq_1022 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.go
d_go_1050 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  AgdaAny ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_1050 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-store-at-slot
d_sim'45'store'45'at'45'slot_1084 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FlatCorr_258
d_sim'45'store'45'at'45'slot_1084 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7
  = du_sim'45'store'45'at'45'slot_1084 v6
du_sim'45'store'45'at'45'slot_1084 ::
  T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'store'45'at'45'slot_1084 v0
  = coe du_corr'45'clean_1110 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.base
d_base_1102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer
d_base_1102 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 = du_base_1102 v5
du_base_1102 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer
du_base_1102 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.Out
d_Out_1104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_Out_1104 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 = du_Out_1104 v4
du_Out_1104 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_Out_1104 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_152
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cf
d_cf_1106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
d_cf_1106 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 = du_cf_1106 v4
du_cf_1106 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> AgdaAny
du_cf_1106 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_586
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_1108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_1108 v0 ~v1 v2 v3 v4 v5 ~v6 ~v7
  = du_xpost_1108 v0 v2 v3 v4 v5
du_xpost_1108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_1108 v0 v1 v2 v3 v4
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
            addInt (coe du_base_1102 (coe v4))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_slot'45'to'45'disp_10
               (coe v2)))
         (coe
            du_enc'45'sv_216 (coe v0) (coe v1) (coe du_Out_1104 (coe v3))))
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
d_corr'45'clean_1110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_FlatCorr_258
d_corr'45'clean_1110 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7
  = du_corr'45'clean_1110 v6
du_corr'45'clean_1110 :: T_FlatCorr_258 -> T_FlatCorr_258
du_corr'45'clean_1110 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-alloc-stack
d_sim'45'alloc'45'stack_1126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_FlatCorr_258
d_sim'45'alloc'45'stack_1126 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9
                             ~v10
  = du_sim'45'alloc'45'stack_1126 v7
du_sim'45'alloc'45'stack_1126 :: T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'alloc'45'stack_1126 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.stk
d_stk_1152 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stk_1152 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-dealloc-stack
d_sim'45'dealloc'45'stack_1180 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_258
d_sim'45'dealloc'45'stack_1180 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
                               ~v9
  = du_sim'45'dealloc'45'stack_1180 v7
du_sim'45'dealloc'45'stack_1180 :: T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'dealloc'45'stack_1180 v0
  = coe
      C_constructor_318 (\ v1 v2 -> coe d_dom'45'fresh_308 v0 v1 v2)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.bad
d_bad_1208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_bad_1208 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-push-frame
d_sim'45'push'45'frame_1246 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_FlatCorr_258
d_sim'45'push'45'frame_1246 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9
                            ~v10 ~v11 ~v12 ~v13 ~v14 ~v15
  = du_sim'45'push'45'frame_1246 v7
du_sim'45'push'45'frame_1246 :: T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'push'45'frame_1246 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-pop-frame
d_sim'45'pop'45'frame_1292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_FlatCorr_258
d_sim'45'pop'45'frame_1292 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 ~v12 ~v13 ~v14 ~v15
  = du_sim'45'pop'45'frame_1292 v6
du_sim'45'pop'45'frame_1292 :: T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'pop'45'frame_1292 v0
  = coe
      C_constructor_318 (\ v1 v2 -> coe d_dom'45'fresh_308 v0 v1 v2)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.bad
d_bad_1328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_bad_1328 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-const
d_sim'45'load'45'const_1366 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 -> T_FlatCorr_258
d_sim'45'load'45'const_1366 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_sim'45'load'45'const_1366 v6
du_sim'45'load'45'const_1366 :: T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'load'45'const_1366 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-load-code-addr
d_sim'45'load'45'code'45'addr_1386 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 -> T_FlatCorr_258
d_sim'45'load'45'code'45'addr_1386 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_sim'45'load'45'code'45'addr_1386 v6
du_sim'45'load'45'code'45'addr_1386 ::
  T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'load'45'code'45'addr_1386 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-save-closure-reg
d_sim'45'save'45'closure'45'reg_1404 ::
  T_FlatCorr_258 -> T_FlatCorr_258
d_sim'45'save'45'closure'45'reg_1404 v0 = coe v0
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.inc-enc
d_inc'45'enc_1420 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inc'45'enc_1420 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.dec-enc
d_dec'45'enc_1430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dec'45'enc_1430 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-reg-input2-inc
d_sim'45'reg'45'input2'45'inc_1444 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_258
d_sim'45'reg'45'input2'45'inc_1444 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
                                   ~v8
  = du_sim'45'reg'45'input2'45'inc_1444 v7
du_sim'45'reg'45'input2'45'inc_1444 ::
  T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'reg'45'input2'45'inc_1444 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-reg-scratch-dec
d_sim'45'reg'45'scratch'45'dec_1472 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_258
d_sim'45'reg'45'scratch'45'dec_1472 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
                                    ~v8
  = du_sim'45'reg'45'scratch'45'dec_1472 v7
du_sim'45'reg'45'scratch'45'dec_1472 ::
  T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'reg'45'scratch'45'dec_1472 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ext-addr-aux
d_ext'45'addr'45'aux_1496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
d_ext'45'addr'45'aux_1496 ~v0 ~v1 v2 v3 ~v4 v5
  = du_ext'45'addr'45'aux_1496 v2 v3 v5
du_ext'45'addr'45'aux_1496 ::
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
du_ext'45'addr'45'aux_1496 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    addInt (coe d_hfront_194 (coe v0))
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_slot'45'to'45'disp_10
                       (coe
                          MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50 (coe v1)))
             else coe seq (coe v4) (coe d_haddr_190 v0 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ext-addr
d_ext'45'addr_1514 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_ext'45'addr_1514 ~v0 ~v1 v2 v3 v4 = du_ext'45'addr_1514 v2 v3 v4
du_ext'45'addr_1514 ::
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
du_ext'45'addr_1514 v0 v1 v2
  = coe
      du_ext'45'addr'45'aux_1496 (coe v0) (coe v2)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48 (coe v2)))
         (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ExtDom
d_ExtDom_1530 a0 a1 a2 a3 a4 a5 = ()
data T_ExtDom_1530
  = C_ext'45'old_1540 AgdaAny |
    C_ext'45'fresh_1542 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ext-addr-old
d_ext'45'addr'45'old_1550 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'old_1550 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.go
d_go_1566 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_1566 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ext-addr-fresh
d_ext'45'addr'45'fresh_1576 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'fresh_1576 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.go
d_go_1592 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_1592 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ext-addr-base
d_ext'45'addr'45'base_1600 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'base_1600 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.+-not-<
d_'43''45'not'45''60'_1610 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'43''45'not'45''60'_1610 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ext-suc-aux
d_ext'45'suc'45'aux_1628 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'suc'45'aux_1628 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.ext-suc
d_ext'45'suc_1654 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'suc_1654 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.extend-view
d_extend'45'view_1672 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  T_HeapView_168
d_extend'45'view_1672 ~v0 ~v1 v2 v3 v4 ~v5
  = du_extend'45'view_1672 v2 v3 v4
du_extend'45'view_1672 ::
  T_HeapView_168 -> Integer -> Integer -> T_HeapView_168
du_extend'45'view_1672 v0 v1 v2
  = coe
      C_mkHV_210 (coe du_ext'45'addr_1514 (coe v0) (coe v1))
      (addInt
         (coe d_hfront_194 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_82 (coe v2)))
      (coe du_below_1688 (coe v0) (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.below
d_below_1688 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_1530 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_below_1688 ~v0 ~v1 v2 ~v3 v4 ~v5 v6 v7
  = du_below_1688 v2 v4 v6 v7
du_below_1688 ::
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_1530 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_below_1688 v0 v1 v2 v3
  = case coe v3 of
      C_ext'45'old_1540 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'60''45'trans'737'_6714
             (coe d_haddr_190 v0 v2) (d_hfront_194 (coe v0))
             (addInt
                (coe d_hfront_194 (coe v0))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_82 (coe v1)))
             (coe d_dom'45'below_208 v0 v2 v4)
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                (coe d_hfront_194 (coe v0)))
      C_ext'45'fresh_1542 v5
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3714
             (coe d_hfront_194 (coe v0))
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'737''45''60'_4240
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80)
                (coe
                   MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50 (coe v2))
                (coe v1) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cross
d_cross_1708 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_cross_1708 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.inj
d_inj_1726 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_1530 ->
  T_ExtDom_1530 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inj_1726 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._._.addr-eq
d_addr'45'eq_1776 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
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
d_addr'45'eq_1776 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._._.off-eq
d_off'45'eq_1778 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
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
d_off'45'eq_1778 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.enc-ext
d_enc'45'ext_1792 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'ext_1792 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.enc-ext-maybe
d_enc'45'ext'45'maybe_1862 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'ext'45'maybe_1862 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-alloc-heap
d_sim'45'alloc'45'heap_1906 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_FlatCorr_258
d_sim'45'alloc'45'heap_1906 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9
                            ~v10 ~v11 ~v12 ~v13 ~v14 ~v15
  = du_sim'45'alloc'45'heap_1906 v6 v8
du_sim'45'alloc'45'heap_1906 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'alloc'45'heap_1906 v0 v1
  = coe C_constructor_318 (coe du_df_1948 (coe v0) (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.st
d_st_1940 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer
d_st_1940 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15
  = du_st_1940 v6
du_st_1940 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> Integer
du_st_1940 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.dfr
d_dfr_1942 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dfr_1942 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15
  = du_dfr_1942 v8
du_dfr_1942 ::
  T_FlatCorr_258 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_dfr_1942 v0 = coe d_dom'45'fresh_308 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.hv'
d_hv''_1944 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_HeapView_168
d_hv''_1944 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15
  = du_hv''_1944 v2 v3 v6
du_hv''_1944 ::
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> T_HeapView_168
du_hv''_1944 v0 v1 v2
  = coe
      du_extend'45'view_1672 (coe v0) (coe du_st_1940 (coe v2)) (coe v1)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.df
d_df_1948 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_1530 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_df_1948 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 v16 v17
  = du_df_1948 v6 v8 v16 v17
du_df_1948 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_1530 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_df_1948 v0 v1 v2 v3
  = case coe v3 of
      C_ext'45'old_1540 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_m'60'n'8658'm'60'1'43'n_3204
             (coe du_dfr_1942 v1 v2 v4)
      C_ext'45'fresh_1542 v5
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe addInt (coe (1 :: Integer)) (coe du_st_1940 (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.hp
d_hp_1958 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_1530 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hp_1958 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-lea-slot
d_sim'45'lea'45'slot_1984 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 -> T_FlatCorr_258
d_sim'45'lea'45'slot_1984 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_sim'45'lea'45'slot_1984 v6
du_sim'45'lea'45'slot_1984 :: T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'lea'45'slot_1984 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cf
d_cf_2000 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 -> AgdaAny
d_cf_2000 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du_cf_2000 v4
du_cf_2000 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> AgdaAny
du_cf_2000 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_586
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.addr-eq
d_addr'45'eq_2002 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_addr'45'eq_2002 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.haddr-offset
d_haddr'45'offset_2014 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'offset_2014 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.enc-offset
d_enc'45'offset_2040 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'offset_2040 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.base-k
d_base'45'k_2060 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  AgdaAny ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_base'45'k_2060 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sim-lea-indexed
d_sim'45'lea'45'indexed_2086 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_258
d_sim'45'lea'45'indexed_2086 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
                             ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_sim'45'lea'45'indexed_2086 v9
du_sim'45'lea'45'indexed_2086 :: T_FlatCorr_258 -> T_FlatCorr_258
du_sim'45'lea'45'indexed_2086 v0
  = coe du_corr'45'clean_2140 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.xpost
d_xpost_2128 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_xpost_2128 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_xpost_2128 v8
du_xpost_2128 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_xpost_2128 v0 = coe v0
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cleanFlat
d_cleanFlat_2130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_cleanFlat_2130 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_cleanFlat_2130 v4 v5 v6
du_cleanFlat_2130 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_cleanFlat_2130 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlat_76
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_476
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_164
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v2)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.du_offsetLoc_92 (coe v0)
                  (coe v1))))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_470
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v2)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_472
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v2)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_474
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v2))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v2))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_74 (coe v2)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reduces
d_reduces_2132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_2132 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-clean
d_corr'45'clean_2140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapView_168 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_FlatCorr_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_258
d_corr'45'clean_2140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_corr'45'clean_2140 v9
du_corr'45'clean_2140 :: T_FlatCorr_258 -> T_FlatCorr_258
du_corr'45'clean_2140 v0
  = coe C_constructor_318 (d_dom'45'fresh_308 (coe v0))
