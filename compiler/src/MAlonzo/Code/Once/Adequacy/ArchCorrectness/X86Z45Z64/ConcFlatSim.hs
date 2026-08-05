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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatComposition
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext
import qualified MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z64
import qualified MAlonzo.Code.Once.Adequacy.FlatEvents
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.RunTrace
import qualified MAlonzo.Code.Once.CCC.Codegen.AllocMin
import qualified MAlonzo.Code.Once.CCC.Codegen.FrameFreeTrace
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.Codegen.LabelScope
import qualified MAlonzo.Code.Once.CCC.Codegen.ShapeTable
import qualified MAlonzo.Code.Once.CCC.Codegen.SlotBudget
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds
import qualified MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF
import qualified MAlonzo.Code.Once.CCC.Machine.FlatStackPtr
import qualified MAlonzo.Code.Once.CCC.Machine.FlatStackSlot
import qualified MAlonzo.Code.Once.CCC.Machine.FlatStoreWF
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.readLoc
d_readLoc_30 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_readLoc_30 ~v0 ~v1 ~v2 ~v3 = du_readLoc_30
du_readLoc_30 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_readLoc_30
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.writeLoc
d_writeLoc_32 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_writeLoc_32 ~v0 v1 ~v2 ~v3 = du_writeLoc_32 v1
du_writeLoc_32 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_writeLoc_32 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_792 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.writeLocToHeap
d_writeLocToHeap_36 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_writeLocToHeap_36 ~v0 ~v1 ~v2 ~v3 = du_writeLocToHeap_36
du_writeLocToHeap_36 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_writeLocToHeap_36
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_784
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.Frame
d_Frame_40 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  ()
d_Frame_40 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.FlatState
d_FlatState_44 a0 a1 a2 a3 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.do-branch
d_do'45'branch_52 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_do'45'branch_52 ~v0 v1 ~v2 ~v3 = du_do'45'branch_52 v1
du_do'45'branch_52 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_do'45'branch_52 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'branch_232 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.do-jump
d_do'45'jump_54 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_do'45'jump_54 ~v0 ~v1 ~v2 ~v3 = du_do'45'jump_54
du_do'45'jump_54 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_do'45'jump_54
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_224
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.fetch
d_fetch_92 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
d_fetch_92 ~v0 ~v1 ~v2 ~v3 = du_fetch_92
du_fetch_92 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
du_fetch_92 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_216
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.find-label
d_find'45'label_100 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'label_100 ~v0 v1 ~v2 ~v3 = du_find'45'label_100 v1
du_find'45'label_100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'label_100 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.flat-exec-instr
d_flat'45'exec'45'instr_112 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_flat'45'exec'45'instr_112 ~v0 v1 ~v2 ~v3
  = du_flat'45'exec'45'instr_112 v1
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
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.FlatState.falloc
d_falloc_176 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_falloc_176 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.FlatState.fclosure
d_fclosure_178 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fclosure_178 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_82 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.FlatState.floc
d_floc_180 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_floc_180 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.FlatState.fpc
d_fpc_182 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> Integer
d_fpc_182 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.FlatState.fret
d_fret_184 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> [Integer]
d_fret_184 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.BlockStep
d_BlockStep_188 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 -> ()
d_BlockStep_188 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.BlockStepAt
d_BlockStepAt_190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 -> ()
d_BlockStepAt_190 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.CompiledCorr
d_CompiledCorr_192 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.b-cmp-reg-imm
d_b'45'cmp'45'reg'45'imm_196 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_b'45'cmp'45'reg'45'imm_196 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.b-mov-reg-imm
d_b'45'mov'45'reg'45'imm_198 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_b'45'mov'45'reg'45'imm_198 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.b-mov-reg-reg
d_b'45'mov'45'reg'45'reg_200 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_b'45'mov'45'reg'45'reg_200 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-alloc-heap
d_block'45'step'45'alloc'45'heap_202 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'alloc'45'heap_202 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'alloc'45'heap_202
du_block'45'step'45'alloc'45'heap_202 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'alloc'45'heap_202 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                      v10 v11 v12 v13 v14 v15
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'alloc'45'heap_2834
      v2 v3 v4 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-alloc-stack
d_block'45'step'45'alloc'45'stack_204 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'alloc'45'stack_204 ~v0 v1 ~v2 ~v3
  = du_block'45'step'45'alloc'45'stack_204 v1
du_block'45'step'45'alloc'45'stack_204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'alloc'45'stack_204 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                       v9 v10 v11 v12 v13 v14 v15
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'alloc'45'stack_1460
      (coe v0) v3 v4 v5 v6 v14
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-c-branch-nz
d_block'45'step'45'c'45'branch'45'nz_206 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'c'45'branch'45'nz_206 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'c'45'branch'45'nz_206
du_block'45'step'45'c'45'branch'45'nz_206 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'c'45'branch'45'nz_206 v0 v1 v2 v3 v4 v5 v6 v7
                                          v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'branch'45'nz_2962
      v3 v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-c-branch-scratch-zero
d_block'45'step'45'c'45'branch'45'scratch'45'zero_208 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'c'45'branch'45'scratch'45'zero_208 ~v0 ~v1 ~v2
                                                      ~v3
  = du_block'45'step'45'c'45'branch'45'scratch'45'zero_208
du_block'45'step'45'c'45'branch'45'scratch'45'zero_208 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'c'45'branch'45'scratch'45'zero_208 v0 v1 v2 v3
                                                       v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'branch'45'scratch'45'zero_2204
      v1 v3 v5 v6 v7
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-c-branch-tag-nz
d_block'45'step'45'c'45'branch'45'tag'45'nz_210 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'c'45'branch'45'tag'45'nz_210 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'c'45'branch'45'tag'45'nz_210
du_block'45'step'45'c'45'branch'45'tag'45'nz_210 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'c'45'branch'45'tag'45'nz_210 v0 v1 v2 v3 v4 v5
                                                 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'branch'45'tag'45'nz_2746
      v3 v6 v7
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-c-branch-tag-zero
d_block'45'step'45'c'45'branch'45'tag'45'zero_212 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'c'45'branch'45'tag'45'zero_212 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'c'45'branch'45'tag'45'zero_212
du_block'45'step'45'c'45'branch'45'tag'45'zero_212 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'c'45'branch'45'tag'45'zero_212 v0 v1 v2 v3 v4
                                                   v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'branch'45'tag'45'zero_2354
      v1 v3 v6 v7 v8
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-c-jmp
d_block'45'step'45'c'45'jmp_214 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'c'45'jmp_214 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'c'45'jmp_214
du_block'45'step'45'c'45'jmp_214 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'c'45'jmp_214 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'jmp_1140
      v1 v3 v5 v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-c-label
d_block'45'step'45'c'45'label_216 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'c'45'label_216 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'c'45'label_216
du_block'45'step'45'c'45'label_216 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'c'45'label_216 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'label_986
      v3 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-count-inc
d_block'45'step'45'count'45'inc_218 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'count'45'inc_218 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'count'45'inc_218
du_block'45'step'45'count'45'inc_218 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'count'45'inc_218 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'count'45'inc_2096
      v3 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-count-zero
d_block'45'step'45'count'45'zero_220 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'count'45'zero_220 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'count'45'zero_220
du_block'45'step'45'count'45'zero_220 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'count'45'zero_220 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'count'45'zero_936
      v3 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-dealloc-stack
d_block'45'step'45'dealloc'45'stack_222 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'dealloc'45'stack_222 ~v0 v1 ~v2 ~v3
  = du_block'45'step'45'dealloc'45'stack_222 v1
du_block'45'step'45'dealloc'45'stack_222 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'dealloc'45'stack_222 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'dealloc'45'stack_1528
      (coe v0) v3 v4 v5 v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-lea-slot
d_block'45'step'45'lea'45'slot_224 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'lea'45'slot_224 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'lea'45'slot_224
du_block'45'step'45'lea'45'slot_224 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'lea'45'slot_224 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'lea'45'slot_2910
      v3 v4 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-load-code-addr
d_block'45'step'45'load'45'code'45'addr_226 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'load'45'code'45'addr_226 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'load'45'code'45'addr_226
du_block'45'step'45'load'45'code'45'addr_226 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'load'45'code'45'addr_226 v0 v1 v2 v3 v4 v5 v6
                                             v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'code'45'addr_1684
      v3 v4 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-load-const
d_block'45'step'45'load'45'const_228 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'load'45'const_228 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'load'45'const_228
du_block'45'step'45'load'45'const_228 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'load'45'const_228 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'const_1584
      v3 v4 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-load-const-float
d_block'45'step'45'load'45'const'45'float_230 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'load'45'const'45'float_230 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'load'45'const'45'float_230
du_block'45'step'45'load'45'const'45'float_230 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'load'45'const'45'float_230 v0 v1 v2 v3 v4 v5 v6
                                               v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'const'45'float_1634
      v3 v4 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-load-from-slot
d_block'45'step'45'load'45'from'45'slot_232 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'load'45'from'45'slot_232 ~v0 v1 ~v2 ~v3
  = du_block'45'step'45'load'45'from'45'slot_232 v1
du_block'45'step'45'load'45'from'45'slot_232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'load'45'from'45'slot_232 v0 v1 v2 v3 v4 v5 v6
                                             v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'from'45'slot_1332
      (coe v0) v1 v4 v6 v7
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-load-indirect
d_block'45'step'45'load'45'indirect_234 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'load'45'indirect_234 ~v0 v1 ~v2 ~v3
  = du_block'45'step'45'load'45'indirect_234 v1
du_block'45'step'45'load'45'indirect_234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'load'45'indirect_234 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'indirect_1200
      (coe v0) v1 v4 v6 v7
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-load-indirect-stack
d_block'45'step'45'load'45'indirect'45'stack_236 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'load'45'indirect'45'stack_236 ~v0 v1 ~v2 ~v3
  = du_block'45'step'45'load'45'indirect'45'stack_236 v1
du_block'45'step'45'load'45'indirect'45'stack_236 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'load'45'indirect'45'stack_236 v0 v1 v2 v3 v4 v5
                                                  v6 v7 v8 v9 v10 v11 v12 v13 v14
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'indirect'45'stack_3040
      (coe v0) v1 v4 v7 v8
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-load-indirect-suc
d_block'45'step'45'load'45'indirect'45'suc_238 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'load'45'indirect'45'suc_238 ~v0 v1 ~v2 ~v3
  = du_block'45'step'45'load'45'indirect'45'suc_238 v1
du_block'45'step'45'load'45'indirect'45'suc_238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'load'45'indirect'45'suc_238 v0 v1 v2 v3 v4 v5
                                                v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'indirect'45'suc_1264
      (coe v0) v1 v4 v6 v7
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-load-indirect-suc-stack
d_block'45'step'45'load'45'indirect'45'suc'45'stack_240 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'load'45'indirect'45'suc'45'stack_240 ~v0 v1 ~v2
                                                        ~v3
  = du_block'45'step'45'load'45'indirect'45'suc'45'stack_240 v1
du_block'45'step'45'load'45'indirect'45'suc'45'stack_240 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'load'45'indirect'45'suc'45'stack_240 v0 v1 v2
                                                         v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'indirect'45'suc'45'stack_3120
      (coe v0) v1 v4 v7 v8
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-load-tag-lit
d_block'45'step'45'load'45'tag'45'lit_242 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'load'45'tag'45'lit_242 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'load'45'tag'45'lit_242
du_block'45'step'45'load'45'tag'45'lit_242 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'load'45'tag'45'lit_242 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'tag'45'lit_862
      v3 v4 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-mov-input2-to-output
d_block'45'step'45'mov'45'input2'45'to'45'output_244 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'mov'45'input2'45'to'45'output_244 ~v0 ~v1 ~v2
                                                     ~v3
  = du_block'45'step'45'mov'45'input2'45'to'45'output_244
du_block'45'step'45'mov'45'input2'45'to'45'output_244 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'mov'45'input2'45'to'45'output_244 v0 v1 v2 v3
                                                      v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'mov'45'input2'45'to'45'output_736
      v3 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-mov-output-to-input2
d_block'45'step'45'mov'45'output'45'to'45'input2_246 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'mov'45'output'45'to'45'input2_246 ~v0 ~v1 ~v2
                                                     ~v3
  = du_block'45'step'45'mov'45'output'45'to'45'input2_246
du_block'45'step'45'mov'45'output'45'to'45'input2_246 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'mov'45'output'45'to'45'input2_246 v0 v1 v2 v3
                                                      v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'mov'45'output'45'to'45'input2_760
      v3 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-mov-ri
d_block'45'step'45'mov'45'ri_248 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'mov'45'ri_248 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'mov'45'ri_248
du_block'45'step'45'mov'45'ri_248 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'mov'45'ri_248 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                  v11 v12
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'mov'45'ri_790
      v3 v5 v6 v12
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-mov-rr
d_block'45'step'45'mov'45'rr_250 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'mov'45'rr_250 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'mov'45'rr_250
du_block'45'step'45'mov'45'rr_250 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'mov'45'rr_250 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                  v11 v12
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'mov'45'rr_618
      v3 v5 v6 v12
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-mov-to-input
d_block'45'step'45'mov'45'to'45'input_252 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'mov'45'to'45'input_252 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'mov'45'to'45'input_252
du_block'45'step'45'mov'45'to'45'input_252 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'mov'45'to'45'input_252 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'mov'45'to'45'input_712
      v3 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-mov-to-output
d_block'45'step'45'mov'45'to'45'output_254 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'mov'45'to'45'output_254 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'mov'45'to'45'output_254
du_block'45'step'45'mov'45'to'45'output_254 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'mov'45'to'45'output_254 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'mov'45'to'45'output_688
      v3 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-reclaim-to
d_block'45'step'45'reclaim'45'to_256 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'reclaim'45'to_256 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'reclaim'45'to_256
du_block'45'step'45'reclaim'45'to_256 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'reclaim'45'to_256 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'reclaim'45'to_1104
      v3 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-restore-input
d_block'45'step'45'restore'45'input_258 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'restore'45'input_258 ~v0 v1 ~v2 ~v3
  = du_block'45'step'45'restore'45'input_258 v1
du_block'45'step'45'restore'45'input_258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'restore'45'input_258 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9 v10 v11
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'restore'45'input_1392
      (coe v0) v1 v4 v6 v7
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-save-closure-reg
d_block'45'step'45'save'45'closure'45'reg_260 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'save'45'closure'45'reg_260 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'save'45'closure'45'reg_260
du_block'45'step'45'save'45'closure'45'reg_260 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'save'45'closure'45'reg_260 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'save'45'closure'45'reg_1732
      v3 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-scratch-dec
d_block'45'step'45'scratch'45'dec_262 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'scratch'45'dec_262 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'scratch'45'dec_262
du_block'45'step'45'scratch'45'dec_262 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'scratch'45'dec_262 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'scratch'45'dec_2148
      v3 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-scratch-load-count
d_block'45'step'45'scratch'45'load'45'count_264 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'scratch'45'load'45'count_264 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'scratch'45'load'45'count_264
du_block'45'step'45'scratch'45'load'45'count_264 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'scratch'45'load'45'count_264 v0 v1 v2 v3 v4 v5
                                                 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'scratch'45'load'45'count_960
      v3 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-scratch-one
d_block'45'step'45'scratch'45'one_266 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'scratch'45'one_266 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'scratch'45'one_266
du_block'45'step'45'scratch'45'one_266 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'scratch'45'one_266 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'scratch'45'one_888
      v3 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-scratch-zero
d_block'45'step'45'scratch'45'zero_268 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'scratch'45'zero_268 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'scratch'45'zero_268
du_block'45'step'45'scratch'45'zero_268 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'scratch'45'zero_268 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'scratch'45'zero_912
      v3 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-store-at-slot
d_block'45'step'45'store'45'at'45'slot_270 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'store'45'at'45'slot_270 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'store'45'at'45'slot_270
du_block'45'step'45'store'45'at'45'slot_270 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'store'45'at'45'slot_270 v0 v1 v2 v3 v4 v5 v6 v7
                                            v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'store'45'at'45'slot_2036
      v2 v3 v4 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-store-indirect
d_block'45'step'45'store'45'indirect_272 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'store'45'indirect_272 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'store'45'indirect_272
du_block'45'step'45'store'45'indirect_272 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'store'45'indirect_272 v0 v1 v2 v3 v4 v5 v6 v7
                                          v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'store'45'indirect_1902
      v2 v3 v4 v5 v9
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-store-indirect-stack
d_block'45'step'45'store'45'indirect'45'stack_274 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'store'45'indirect'45'stack_274 ~v0 v1 ~v2 ~v3
  = du_block'45'step'45'store'45'indirect'45'stack_274 v1
du_block'45'step'45'store'45'indirect'45'stack_274 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'store'45'indirect'45'stack_274 v0 v1 v2 v3 v4
                                                   v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'store'45'indirect'45'stack_3204
      (coe v0) v1 v3 v4 v6 v7
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-store-indirect-suc
d_block'45'step'45'store'45'indirect'45'suc_276 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'store'45'indirect'45'suc_276 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'store'45'indirect'45'suc_276
du_block'45'step'45'store'45'indirect'45'suc_276 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'store'45'indirect'45'suc_276 v0 v1 v2 v3 v4 v5
                                                 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'store'45'indirect'45'suc_1966
      v2 v3 v4 v5 v9
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-store-indirect-suc-stack
d_block'45'step'45'store'45'indirect'45'suc'45'stack_278 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'store'45'indirect'45'suc'45'stack_278 ~v0 v1 ~v2
                                                         ~v3
  = du_block'45'step'45'store'45'indirect'45'suc'45'stack_278 v1
du_block'45'step'45'store'45'indirect'45'suc'45'stack_278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'store'45'indirect'45'suc'45'stack_278 v0 v1 v2
                                                          v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'store'45'indirect'45'suc'45'stack_3288
      (coe v0) v1 v3 v4 v6 v7
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-worklist-check
d_block'45'step'45'worklist'45'check_280 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'worklist'45'check_280 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'worklist'45'check_280
du_block'45'step'45'worklist'45'check_280 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'worklist'45'check_280 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'worklist'45'check_1070
      v3 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-worklist-init
d_block'45'step'45'worklist'45'init_282 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'worklist'45'init_282 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'worklist'45'init_282
du_block'45'step'45'worklist'45'init_282 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'worklist'45'init_282 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'worklist'45'init_1036
      v3 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-worklist-pop
d_block'45'step'45'worklist'45'pop_284 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'worklist'45'pop_284 ~v0 v1 ~v2 ~v3
  = du_block'45'step'45'worklist'45'pop_284 v1
du_block'45'step'45'worklist'45'pop_284 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'worklist'45'pop_284 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'worklist'45'pop_1844
      (coe v0) v1 v4 v6 v7
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-worklist-push
d_block'45'step'45'worklist'45'push_286 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'worklist'45'push_286 ~v0 ~v1 ~v2 ~v3
  = du_block'45'step'45'worklist'45'push_286
du_block'45'step'45'worklist'45'push_286 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'worklist'45'push_286 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'worklist'45'push_1782
      v2 v3 v4 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.dataCorr
d_dataCorr_288 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dataCorr_288 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.d_dataCorr_524
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.load-indirect-heap-empty-stuck
d_load'45'indirect'45'heap'45'empty'45'stuck_290 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'heap'45'empty'45'stuck_290 ~v0 ~v1 ~v2 ~v3
  = du_load'45'indirect'45'heap'45'empty'45'stuck_290
du_load'45'indirect'45'heap'45'empty'45'stuck_290 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'heap'45'empty'45'stuck_290 v0 v1 v2 v3 v4 v5
                                                  v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_load'45'indirect'45'heap'45'empty'45'stuck_2502
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.load-indirect-stack-empty-stuck
d_load'45'indirect'45'stack'45'empty'45'stuck_292 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'stack'45'empty'45'stuck_292 ~v0 ~v1 ~v2 ~v3
  = du_load'45'indirect'45'stack'45'empty'45'stuck_292
du_load'45'indirect'45'stack'45'empty'45'stuck_292 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'stack'45'empty'45'stuck_292 v0 v1 v2 v3 v4
                                                   v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_load'45'indirect'45'stack'45'empty'45'stuck_2556
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.load-indirect-suc-heap-empty-stuck
d_load'45'indirect'45'suc'45'heap'45'empty'45'stuck_294 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'heap'45'empty'45'stuck_294 ~v0 ~v1 ~v2
                                                        ~v3
  = du_load'45'indirect'45'suc'45'heap'45'empty'45'stuck_294
du_load'45'indirect'45'suc'45'heap'45'empty'45'stuck_294 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'heap'45'empty'45'stuck_294 v0 v1 v2
                                                         v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_load'45'indirect'45'suc'45'heap'45'empty'45'stuck_2618
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.load-indirect-suc-stack-empty-stuck
d_load'45'indirect'45'suc'45'stack'45'empty'45'stuck_296 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'stack'45'empty'45'stuck_296 ~v0 ~v1
                                                         ~v2 ~v3
  = du_load'45'indirect'45'suc'45'stack'45'empty'45'stuck_296
du_load'45'indirect'45'suc'45'stack'45'empty'45'stuck_296 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'stack'45'empty'45'stuck_296 v0 v1 v2
                                                          v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_load'45'indirect'45'suc'45'stack'45'empty'45'stuck_2676
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.pc-off
d_pc'45'off_298 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pc'45'off_298 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.+-not-<
d_'43''45'not'45''60'_302 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'43''45'not'45''60'_302 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.AddrMap
d_AddrMap_304 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  ()
d_AddrMap_304 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.ExtDom
d_ExtDom_306 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr
d_FlatCorr_308 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.HDom
d_HDom_312 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> ()
d_HDom_312 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.HeapView
d_HeapView_314 a0 a1 a2 a3 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.StackWindows
d_StackWindows_318 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_StackWindows_318 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.Window
d_Window_320 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  AgdaAny -> Integer -> ()
d_Window_320 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.atstack-frame-inj
d_atstack'45'frame'45'inj_322 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atstack'45'frame'45'inj_322 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.atstack-slot-inj
d_atstack'45'slot'45'inj_324 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atstack'45'slot'45'inj_324 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.dec-enc
d_dec'45'enc_326 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dec'45'enc_326 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.descend-view
d_descend'45'view_328 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218
d_descend'45'view_328 ~v0 ~v1 ~v2 ~v3 = du_descend'45'view_328
du_descend'45'view_328 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218
du_descend'45'view_328 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_descend'45'view_586
      v0 v1 v3
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.dom-below
d_dom'45'below_330 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_330 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'below_262
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.dom-fresh
d_dom'45'fresh_332 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'fresh_332 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'fresh_436
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.dom-sized
d_dom'45'sized_334 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_dom'45'sized_334 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'sized_446
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.dom-written
d_dom'45'written_336 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_dom'45'written_336 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'written_442
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.enc-ext
d_enc'45'ext_338 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'ext_338 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.enc-ext-maybe
d_enc'45'ext'45'maybe_340 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'ext'45'maybe_340 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.enc-maybe
d_enc'45'maybe_342 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
d_enc'45'maybe_342 ~v0 v1 ~v2 ~v3 = du_enc'45'maybe_342 v1
du_enc'45'maybe_342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
du_enc'45'maybe_342 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_enc'45'maybe_316
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.enc-maybe-at
d_enc'45'maybe'45'at_344 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
d_enc'45'maybe'45'at_344 ~v0 v1 ~v2 ~v3
  = du_enc'45'maybe'45'at_344 v1
du_enc'45'maybe'45'at_344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
du_enc'45'maybe'45'at_344 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_enc'45'maybe'45'at_304
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.enc-sv
d_enc'45'sv_346 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
d_enc'45'sv_346 ~v0 v1 ~v2 ~v3 = du_enc'45'sv_346 v1
du_enc'45'sv_346 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
du_enc'45'sv_346 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_enc'45'sv_312
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.enc-sv-at
d_enc'45'sv'45'at_348 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
d_enc'45'sv'45'at_348 ~v0 v1 ~v2 ~v3 = du_enc'45'sv'45'at_348 v1
du_enc'45'sv'45'at_348 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
du_enc'45'sv'45'at_348 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_enc'45'sv'45'at_276
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.enc-zero
d_enc'45'zero_350 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'zero_350 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.ext-addr
d_ext'45'addr_352 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_ext'45'addr_352 ~v0 ~v1 ~v2 ~v3 = du_ext'45'addr_352
du_ext'45'addr_352 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
du_ext'45'addr_352
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_ext'45'addr_2184
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.ext-addr-aux
d_ext'45'addr'45'aux_354 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
d_ext'45'addr'45'aux_354 ~v0 ~v1 ~v2 ~v3
  = du_ext'45'addr'45'aux_354
du_ext'45'addr'45'aux_354 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
du_ext'45'addr'45'aux_354 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_ext'45'addr'45'aux_2166
      v0 v1 v3
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.ext-addr-base
d_ext'45'addr'45'base_356 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'base_356 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.ext-addr-fresh
d_ext'45'addr'45'fresh_358 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'fresh_358 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.ext-addr-old
d_ext'45'addr'45'old_360 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'old_360 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.ext-suc
d_ext'45'suc_366 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'suc_366 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.ext-suc-aux
d_ext'45'suc'45'aux_368 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'suc'45'aux_368 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.extend-view
d_extend'45'view_370 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218
d_extend'45'view_370 ~v0 ~v1 ~v2 ~v3 = du_extend'45'view_370
du_extend'45'view_370 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218
du_extend'45'view_370 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_extend'45'view_2342
      v0 v1 v2 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.frames-of
d_frames'45'of_372 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_frames'45'of_372 ~v0 ~v1 ~v2 ~v3 = du_frames'45'of_372
du_frames'45'of_372 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_frames'45'of_372
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_frames'45'of_320
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.front-lo
d_front'45'lo_374 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo_374 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_front'45'lo_266
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.haddr
d_haddr_376 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_haddr_376 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_haddr_244
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.haddr-inj
d_haddr'45'inj_378 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_378 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.haddr-suc
d_haddr'45'suc_380 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_380 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.halt-eq
d_halt'45'eq_382 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45'eq_382 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.heap-eq
d_heap'45'eq_384 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'eq_384 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.hfront
d_hfront_386 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer
d_hfront_386 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_hfront_248
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.inc-enc
d_inc'45'enc_388 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inc'45'enc_388 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.lit-word
d_lit'45'word_390 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer -> Integer
d_lit'45'word_390 ~v0 ~v1 ~v2 ~v3 v4 = du_lit'45'word_390 v4
du_lit'45'word_390 :: Integer -> Integer
du_lit'45'word_390 v0 = coe v0
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.lo
d_lo_392 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer
d_lo_392 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_lo_264
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.lo-le
d_lo'45'le_394 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'le_394 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_lo'45'le_452
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.r14-eq
d_r14'45'eq_398 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r14'45'eq_398 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.r15-eq
d_r15'45'eq_400 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r15'45'eq_400 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.rax-eq
d_rax'45'eq_402 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rax'45'eq_402 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.rbx-eq
d_rbx'45'eq_404 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rbx'45'eq_404 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.rdi-eq
d_rdi'45'eq_406 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45'eq_406 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.read-write-miss
d_read'45'write'45'miss_408 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'write'45'miss_408 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.rsi-eq
d_rsi'45'eq_410 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rsi'45'eq_410 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.rsp-eq
d_rsp'45'eq_412 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rsp'45'eq_412 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sep
d_sep_414 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sep_414 v0 ~v1 ~v2 v3 = du_sep_414 v0 v3
du_sep_414 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sep_414 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_front'45'lo_266
         (coe v0))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_lo'45'le_452
         (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-alloc-heap
d_sim'45'alloc'45'heap_416 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'alloc'45'heap_416 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'alloc'45'heap_416
du_sim'45'alloc'45'heap_416 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'alloc'45'heap_416 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12 v13 v14
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'alloc'45'heap_2680
      v4 v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-alloc-stack
d_sim'45'alloc'45'stack_418 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'alloc'45'stack_418 ~v0 v1 ~v2 ~v3
  = du_sim'45'alloc'45'stack_418 v1
du_sim'45'alloc'45'stack_418 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'alloc'45'stack_418 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12 v13
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'alloc'45'stack_1916
      (coe v0) v2 v4 v6 v12
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-dealloc-stack
d_sim'45'dealloc'45'stack_420 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'dealloc'45'stack_420 ~v0 v1 ~v2 ~v3
  = du_sim'45'dealloc'45'stack_420 v1
du_sim'45'dealloc'45'stack_420 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'dealloc'45'stack_420 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'dealloc'45'stack_1980
      (coe v0) v4 v5 v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-lea-slot
d_sim'45'lea'45'slot_422 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'lea'45'slot_422 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'lea'45'slot_422
du_sim'45'lea'45'slot_422 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'lea'45'slot_422 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'lea'45'slot_2796
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-load-code-addr
d_sim'45'load'45'code'45'addr_424 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'load'45'code'45'addr_424 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'load'45'code'45'addr_424
du_sim'45'load'45'code'45'addr_424 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'code'45'addr_424 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'code'45'addr_2056
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-load-const
d_sim'45'load'45'const_426 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'load'45'const_426 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'load'45'const_426
du_sim'45'load'45'const_426 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'const_426 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'const_2016
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-load-const-float
d_sim'45'load'45'const'45'float_428 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'load'45'const'45'float_428 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'load'45'const'45'float_428
du_sim'45'load'45'const'45'float_428 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'const'45'float_428 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'const'45'float_2036
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-load-from-slot
d_sim'45'load'45'from'45'slot_430 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'load'45'from'45'slot_430 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'load'45'from'45'slot_430
du_sim'45'load'45'from'45'slot_430 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'from'45'slot_430 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'from'45'slot_898
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-load-indirect
d_sim'45'load'45'indirect_432 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'load'45'indirect_432 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'load'45'indirect_432
du_sim'45'load'45'indirect_432 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'indirect_432 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'indirect_848
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-load-indirect-stack
d_sim'45'load'45'indirect'45'stack_434 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'load'45'indirect'45'stack_434 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'load'45'indirect'45'stack_434
du_sim'45'load'45'indirect'45'stack_434 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'indirect'45'stack_434 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'indirect'45'stack_2832
      v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-load-indirect-suc
d_sim'45'load'45'indirect'45'suc_436 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'load'45'indirect'45'suc_436 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'load'45'indirect'45'suc_436
du_sim'45'load'45'indirect'45'suc_436 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'indirect'45'suc_436 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'indirect'45'suc_798
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-load-indirect-suc-stack
d_sim'45'load'45'indirect'45'suc'45'stack_438 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'load'45'indirect'45'suc'45'stack_438 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'load'45'indirect'45'suc'45'stack_438
du_sim'45'load'45'indirect'45'suc'45'stack_438 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'indirect'45'suc'45'stack_438 v0 v1 v2 v3 v4 v5 v6
                                               v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'indirect'45'suc'45'stack_2886
      v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-load-tag-lit
d_sim'45'load'45'tag'45'lit_440 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'load'45'tag'45'lit_440 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'load'45'tag'45'lit_440
du_sim'45'load'45'tag'45'lit_440 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'tag'45'lit_440 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'tag'45'lit_698
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-mov-input2-to-output
d_sim'45'mov'45'input2'45'to'45'output_442 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'mov'45'input2'45'to'45'output_442 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'mov'45'input2'45'to'45'output_442
du_sim'45'mov'45'input2'45'to'45'output_442 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'mov'45'input2'45'to'45'output_442 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'mov'45'input2'45'to'45'output_664
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-mov-output-to-input2
d_sim'45'mov'45'output'45'to'45'input2_444 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'mov'45'output'45'to'45'input2_444 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'mov'45'output'45'to'45'input2_444
du_sim'45'mov'45'output'45'to'45'input2_444 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'mov'45'output'45'to'45'input2_444 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'mov'45'output'45'to'45'input2_680
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-mov-to-input
d_sim'45'mov'45'to'45'input_446 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'mov'45'to'45'input_446 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'mov'45'to'45'input_446
du_sim'45'mov'45'to'45'input_446 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'mov'45'to'45'input_446 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'mov'45'to'45'input_648
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-mov-to-output
d_sim'45'mov'45'to'45'output_448 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'mov'45'to'45'output_448 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'mov'45'to'45'output_448
du_sim'45'mov'45'to'45'output_448 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'mov'45'to'45'output_448 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'mov'45'to'45'output_632
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-reg-count-inc
d_sim'45'reg'45'count'45'inc_450 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'reg'45'count'45'inc_450 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'reg'45'count'45'inc_450
du_sim'45'reg'45'count'45'inc_450 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'reg'45'count'45'inc_450 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'count'45'inc_2114
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-reg-count-zero
d_sim'45'reg'45'count'45'zero_452 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'reg'45'count'45'zero_452 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'reg'45'count'45'zero_452
du_sim'45'reg'45'count'45'zero_452 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'reg'45'count'45'zero_452 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'count'45'zero_748
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-reg-scratch-dec
d_sim'45'reg'45'scratch'45'dec_454 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'reg'45'scratch'45'dec_454 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'reg'45'scratch'45'dec_454
du_sim'45'reg'45'scratch'45'dec_454 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'reg'45'scratch'45'dec_454 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'scratch'45'dec_2142
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-reg-scratch-load-count
d_sim'45'reg'45'scratch'45'load'45'count_456 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'reg'45'scratch'45'load'45'count_456 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'reg'45'scratch'45'load'45'count_456
du_sim'45'reg'45'scratch'45'load'45'count_456 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'reg'45'scratch'45'load'45'count_456 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'scratch'45'load'45'count_764
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-reg-scratch-one
d_sim'45'reg'45'scratch'45'one_458 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'reg'45'scratch'45'one_458 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'reg'45'scratch'45'one_458
du_sim'45'reg'45'scratch'45'one_458 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'reg'45'scratch'45'one_458 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'scratch'45'one_716
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-reg-scratch-zero
d_sim'45'reg'45'scratch'45'zero_460 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'reg'45'scratch'45'zero_460 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'reg'45'scratch'45'zero_460
du_sim'45'reg'45'scratch'45'zero_460 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'reg'45'scratch'45'zero_460 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'scratch'45'zero_732
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-restore-input
d_sim'45'restore'45'input_462 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'restore'45'input_462 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'restore'45'input_462
du_sim'45'restore'45'input_462 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'restore'45'input_462 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'restore'45'input_1592
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-save-closure-reg
d_sim'45'save'45'closure'45'reg_464 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'save'45'closure'45'reg_464 v0 = coe v0
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-store-at-slot
d_sim'45'store'45'at'45'slot_466 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'store'45'at'45'slot_466 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'store'45'at'45'slot_466
du_sim'45'store'45'at'45'slot_466 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'store'45'at'45'slot_466 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'store'45'at'45'slot_1864
      v2 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-store-indirect
d_sim'45'store'45'indirect_468 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'store'45'indirect_468 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'store'45'indirect_468
du_sim'45'store'45'indirect_468 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'store'45'indirect_468 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'store'45'indirect_1494
      v1 v2 v4 v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-store-indirect-stack
d_sim'45'store'45'indirect'45'stack_470 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'store'45'indirect'45'stack_470 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'store'45'indirect'45'stack_470
du_sim'45'store'45'indirect'45'stack_470 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'store'45'indirect'45'stack_470 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'store'45'indirect'45'stack_2938
      v2 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-store-indirect-suc
d_sim'45'store'45'indirect'45'suc_472 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'store'45'indirect'45'suc_472 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'store'45'indirect'45'suc_472
du_sim'45'store'45'indirect'45'suc_472 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'store'45'indirect'45'suc_472 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'store'45'indirect'45'suc_1542
      v1 v2 v4 v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-store-indirect-suc-stack
d_sim'45'store'45'indirect'45'suc'45'stack_474 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'store'45'indirect'45'suc'45'stack_474 ~v0 ~v1 ~v2 ~v3
  = du_sim'45'store'45'indirect'45'suc'45'stack_474
du_sim'45'store'45'indirect'45'suc'45'stack_474 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'store'45'indirect'45'suc'45'stack_474 v0 v1 v2 v3 v4 v5
                                                v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'store'45'indirect'45'suc'45'stack_2994
      v2 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.slot-addr-inj
d_slot'45'addr'45'inj_476 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'inj_476 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.stack-eq
d_stack'45'eq_478 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'eq_478 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_stack'45'eq_458
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.stack-eq-cur
d_stack'45'eq'45'cur_480 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'eq'45'cur_480 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.stack-eq-win
d_stack'45'eq'45'win_482 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'eq'45'win_482 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.store-dom-written
d_store'45'dom'45'written_484 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
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
d_store'45'dom'45'written_484 ~v0 ~v1 ~v2 ~v3
  = du_store'45'dom'45'written_484
du_store'45'dom'45'written_484 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
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
du_store'45'dom'45'written_484 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_store'45'dom'45'written_1160
      v1 v4 v5 v6 v7 v8
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.store-heap-eq
d_store'45'heap'45'eq_486 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'heap'45'eq_486 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.store-slot-heap-eq
d_store'45'slot'45'heap'45'eq_488 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
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
d_store'45'slot'45'heap'45'eq_488 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.store-slot-stack-eq
d_store'45'slot'45'stack'45'eq_490 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
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
d_store'45'slot'45'stack'45'eq_490 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sv-tag-zero
d_sv'45'tag'45'zero_492 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sv'45'tag'45'zero_492 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.untouched
d_untouched_494 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched_494 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.untouched-descend
d_untouched'45'descend_496 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'descend_496 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.untouched-heap-store
d_untouched'45'heap'45'store_498 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'heap'45'store_498 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.untouched-stack-store
d_untouched'45'stack'45'store_500 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'stack'45'store_500 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.untouched-write
d_untouched'45'write_502 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'write_502 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.win-at
d_win'45'at_504 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
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
d_win'45'at_504 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.win-off
d_win'45'off_506 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
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
d_win'45'off_506 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.windows-above
d_windows'45'above_508 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
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
d_windows'45'above_508 ~v0 ~v1 ~v2 ~v3 = du_windows'45'above_508
du_windows'45'above_508 ::
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
du_windows'45'above_508 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_windows'45'above_1350
      v6 v9
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.windows-enc-ext
d_windows'45'enc'45'ext_510 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
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
d_windows'45'enc'45'ext_510 ~v0 ~v1 ~v2 ~v3
  = du_windows'45'enc'45'ext_510
du_windows'45'enc'45'ext_510 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
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
du_windows'45'enc'45'ext_510 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_windows'45'enc'45'ext_2600
      v8 v10
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.windows-heap-store
d_windows'45'heap'45'store_512 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'heap'45'store_512 ~v0 ~v1 ~v2 ~v3
  = du_windows'45'heap'45'store_512
du_windows'45'heap'45'store_512 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'heap'45'store_512 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_windows'45'heap'45'store_1470
      v1 v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.windows-leave
d_windows'45'leave_514 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
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
d_windows'45'leave_514 ~v0 v1 ~v2 ~v3 = du_windows'45'leave_514 v1
du_windows'45'leave_514 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
du_windows'45'leave_514 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_windows'45'leave_1284
      (coe v0) v4 v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.windows-reanchor
d_windows'45'reanchor_516 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
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
d_windows'45'reanchor_516 ~v0 ~v1 ~v2 ~v3
  = du_windows'45'reanchor_516
du_windows'45'reanchor_516 ::
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
du_windows'45'reanchor_516 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_windows'45'reanchor_1256
      v8 v9
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.windows-slot-store
d_windows'45'slot'45'store_518 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
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
d_windows'45'slot'45'store_518 ~v0 ~v1 ~v2 ~v3
  = du_windows'45'slot'45'store_518
du_windows'45'slot'45'store_518 ::
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
du_windows'45'slot'45'store_518 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_windows'45'slot'45'store_1796
      v8 v10
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.windows-write-below
d_windows'45'write'45'below_520 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
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
d_windows'45'write'45'below_520 ~v0 ~v1 ~v2 ~v3
  = du_windows'45'write'45'below_520
du_windows'45'write'45'below_520 ::
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
du_windows'45'write'45'below_520 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_windows'45'write'45'below_1428
      v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.≡ᵇ-refl
d_'8801''7495''45'refl_522 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_522 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.≢→≡ᵇfalse
d_'8802''8594''8801''7495'false_524 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8802''8594''8801''7495'false_524 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.dom-fresh
d_dom'45'fresh_534 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'fresh_534 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'fresh_436
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.dom-sized
d_dom'45'sized_536 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_dom'45'sized_536 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'sized_446
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.dom-written
d_dom'45'written_538 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_dom'45'written_538 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'written_442
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.halt-eq
d_halt'45'eq_540 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45'eq_540 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.heap-eq
d_heap'45'eq_542 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'eq_542 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.lo-le
d_lo'45'le_544 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'le_544 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_lo'45'le_452
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.r14-eq
d_r14'45'eq_546 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r14'45'eq_546 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.r15-eq
d_r15'45'eq_548 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r15'45'eq_548 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.rax-eq
d_rax'45'eq_550 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rax'45'eq_550 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.rbx-eq
d_rbx'45'eq_552 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rbx'45'eq_552 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.rdi-eq
d_rdi'45'eq_554 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45'eq_554 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.rsi-eq
d_rsi'45'eq_556 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rsi'45'eq_556 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.rsp-eq
d_rsp'45'eq_558 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rsp'45'eq_558 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.stack-eq
d_stack'45'eq_560 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'eq_560 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_stack'45'eq_458
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.untouched
d_untouched_562 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched_562 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.HeapView.HDom
d_HDom_566 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> ()
d_HDom_566 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.HeapView.dom-below
d_dom'45'below_568 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_568 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'below_262
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.HeapView.front-lo
d_front'45'lo_570 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo_570 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_front'45'lo_266
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.HeapView.haddr
d_haddr_572 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_haddr_572 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_haddr_244
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.HeapView.haddr-inj
d_haddr'45'inj_574 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_574 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.HeapView.haddr-suc
d_haddr'45'suc_576 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_576 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.HeapView.hfront
d_hfront_578 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer
d_hfront_578 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_hfront_248
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.HeapView.lo
d_lo_580 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer
d_lo_580 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_lo_264
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.CompiledCorr.dataCorr
d_dataCorr_584 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dataCorr_584 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.d_dataCorr_524
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.CompiledCorr.pc-off
d_pc'45'off_586 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pc'45'off_586 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.FlatWF
d_FlatWF_590 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_FlatWF_590 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.sv-below
d_sv'45'below_594 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_sv'45'below_594 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.FlatRegTag
d_FlatRegTag_608 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_FlatRegTag_608 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.x86-len
d_x86'45'len_632 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Integer
d_x86'45'len_632 ~v0 ~v1 ~v2 ~v3 = du_x86'45'len_632
du_x86'45'len_632 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Integer
du_x86'45'len_632
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatComposition.du_x86'45'len_156
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.ir-stack-budget
d_ir'45'stack'45'budget_638 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget_638 v0 ~v1 ~v2 ~v3
  = du_ir'45'stack'45'budget_638 v0
du_ir'45'stack'45'budget_638 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
du_ir'45'stack'45'budget_638 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_702
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.ir-to-trace
d_ir'45'to'45'trace_640 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
d_ir'45'to'45'trace_640 v0 ~v1 ~v2 ~v3
  = du_ir'45'to'45'trace_640 v0
du_ir'45'to'45'trace_640 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
du_ir'45'to'45'trace_640 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_684
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.StackPtrOK
d_StackPtrOK_654 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_StackPtrOK_654 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.StackPtrWF
d_StackPtrWF_658 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_StackPtrWF_658 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.PtrB
d_PtrB_670 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_PtrB_670 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.PtrBoundsWF
d_PtrBoundsWF_674 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_PtrBoundsWF_674 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.AllocMinI
d_AllocMinI_698 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 -> ()
d_AllocMinI_698 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.Meets
d_Meets_704 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_Meets_704 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.mention-at
d_mention'45'at_718 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_mention'45'at_718 ~v0 ~v1 ~v2 ~v3 = du_mention'45'at_718
du_mention'45'at_718 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_mention'45'at_718
  = coe
      MAlonzo.Code.Once.CCC.Codegen.LabelScope.du_mention'45'at_1008
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.once-label-of
d_once'45'label'45'of_722 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_once'45'label'45'of_722 ~v0 ~v1 ~v2 ~v3
  = du_once'45'label'45'of_722
du_once'45'label'45'of_722 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_once'45'label'45'of_722
  = coe
      MAlonzo.Code.Once.CCC.Codegen.LabelScope.du_once'45'label'45'of_138
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.SegState
d_SegState_726 a0 a1 a2 a3 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.is-id?
d_is'45'id'63'_742 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Codegen.SlotBudget.T_SegAction_226 -> Bool
d_is'45'id'63'_742 ~v0 ~v1 ~v2 ~v3 = du_is'45'id'63'_742
du_is'45'id'63'_742 ::
  MAlonzo.Code.Once.CCC.Codegen.SlotBudget.T_SegAction_226 -> Bool
du_is'45'id'63'_742
  = coe MAlonzo.Code.Once.CCC.Codegen.SlotBudget.du_is'45'id'63'_456
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.seg-action
d_seg'45'action_750 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotBudget.T_SegAction_226
d_seg'45'action_750 ~v0 ~v1 ~v2 ~v3 = du_seg'45'action_750
du_seg'45'action_750 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotBudget.T_SegAction_226
du_seg'45'action_750
  = coe MAlonzo.Code.Once.CCC.Codegen.SlotBudget.du_seg'45'action_234
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.seg-at
d_seg'45'at_752 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.SlotBudget.T_SegState_214 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotBudget.T_SegState_214
d_seg'45'at_752 ~v0 ~v1 ~v2 ~v3 = du_seg'45'at_752
du_seg'45'at_752 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.SlotBudget.T_SegState_214 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotBudget.T_SegState_214
du_seg'45'at_752
  = coe MAlonzo.Code.Once.CCC.Codegen.SlotBudget.du_seg'45'at_1982
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.seg-step
d_seg'45'step_758 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotBudget.T_SegState_214 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotBudget.T_SegState_214
d_seg'45'step_758 ~v0 ~v1 ~v2 ~v3 = du_seg'45'step_758
du_seg'45'step_758 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotBudget.T_SegState_214 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotBudget.T_SegState_214
du_seg'45'step_758
  = coe MAlonzo.Code.Once.CCC.Codegen.SlotBudget.du_seg'45'step_256
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.trace-lookup
d_trace'45'lookup_760 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
d_trace'45'lookup_760 ~v0 ~v1 ~v2 ~v3 = du_trace'45'lookup_760
du_trace'45'lookup_760 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
du_trace'45'lookup_760
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotBudget.du_trace'45'lookup_1972
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.SegState.cur
d_cur_764 ::
  MAlonzo.Code.Once.CCC.Codegen.SlotBudget.T_SegState_214 -> Integer
d_cur_764 v0
  = coe MAlonzo.Code.Once.CCC.Codegen.SlotBudget.d_cur_220 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.SegState.saved
d_saved_766 ::
  MAlonzo.Code.Once.CCC.Codegen.SlotBudget.T_SegState_214 ->
  [Integer]
d_saved_766 v0
  = coe MAlonzo.Code.Once.CCC.Codegen.SlotBudget.d_saved_222 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.nonhalt-noncall
d_nonhalt'45'noncall_776 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nonhalt'45'noncall_776 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.t≢f
d_t'8802'f_938 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_t'8802'f_938 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.n≢j
d_n'8802'j_944 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8802'j_944 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.Emitted
d_Emitted_948 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] -> ()
d_Emitted_948 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.EntryLike
d_EntryLike_950 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_EntryLike_950 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.Reachable
d_Reachable_952 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.RunAt
d_RunAt_954 a0 a1 a2 a3 a4 a5 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.run-emit
d_run'45'emit_964 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'emit_964 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.run-emitted
d_run'45'emitted_966 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'emitted_966 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'ir_226
         (coe v0))
      erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.run-heap
d_run'45'heap_968 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  AgdaAny
d_run'45'heap_968 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'heap_230
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.run-ir
d_run'45'ir_970 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_run'45'ir_970 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'ir_226
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.run-reach
d_run'45'reach_972 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186
d_run'45'reach_972 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'reach_232
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.RunAt.run-emit
d_run'45'emit_982 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'emit_982 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.RunAt.run-heap
d_run'45'heap_984 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  AgdaAny
d_run'45'heap_984 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'heap_230
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.RunAt.run-ir
d_run'45'ir_986 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_run'45'ir_986 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'ir_226
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.RunAt.run-reach
d_run'45'reach_988 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186
d_run'45'reach_988 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'reach_232
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.FlatInv
d_FlatInv_998 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_FlatInv_998
  = C_mkFlatInv_1028 MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506
                     MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_314
                     MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.FlatInv.inv-wf
d_inv'45'wf_1018 ::
  T_FlatInv_998 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506
d_inv'45'wf_1018 v0
  = case coe v0 of
      C_mkFlatInv_1028 v1 v2 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.FlatInv.inv-regtag
d_inv'45'regtag_1020 ::
  T_FlatInv_998 ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_314
d_inv'45'regtag_1020 v0
  = case coe v0 of
      C_mkFlatInv_1028 v1 v2 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.FlatInv.inv-ev
d_inv'45'ev_1022 ::
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv'45'ev_1022 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.FlatInv.inv-env
d_inv'45'env_1024 ::
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv'45'env_1024 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.FlatInv.inv-run
d_inv'45'run_1026 ::
  T_FlatInv_998 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212
d_inv'45'run_1026 v0
  = case coe v0 of
      C_mkFlatInv_1028 v1 v2 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.frame-op-absurd
d_frame'45'op'45'absurd_1038 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_frame'45'op'45'absurd_1038 v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 ~v9
  = du_frame'45'op'45'absurd_1038 v0 v5 v7 v8
du_frame'45'op'45'absurd_1038 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> AgdaAny
du_frame'45'op'45'absurd_1038 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.FrameFreeTrace.du_fetch'45'frame'45'free_752
             v0 (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
             (coe MAlonzo.Code.Once.IRTy.C_Unit_16) v4 v3
             (MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v1)) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.flat-inv-step
d_flat'45'inv'45'step_1060 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_FlatInv_998 -> T_FlatInv_998
d_flat'45'inv'45'step_1060 ~v0 v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 ~v10
                           v11
  = du_flat'45'inv'45'step_1060 v1 v6 v7 v8 v11
du_flat'45'inv'45'step_1060 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatInv_998 -> T_FlatInv_998
du_flat'45'inv'45'step_1060 v0 v1 v2 v3 v4
  = coe
      C_mkFlatInv_1028
      (MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_flat'45'wf'45'step_2064
         (coe v0) (coe v1) (coe v2) (coe v3)
         (coe d_inv'45'wf_1018 (coe v4)))
      (MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.d_flat'45'regtag'45'step_1406
         (coe v0) (coe v1) (coe v2) (coe v3)
         (coe d_inv'45'regtag_1020 (coe v4)))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_mkRunAt_234
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'ir_226
            (coe d_inv'45'run_1026 (coe v4)))
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'heap_230
            (coe d_inv'45'run_1026 (coe v4)))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_reach'45'step_200
            v1 v3
            (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'reach_232
               (coe d_inv'45'run_1026 (coe v4)))))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.above-frontier-disj
d_above'45'frontier'45'disj_1080 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_above'45'frontier'45'disj_1080 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.slot-heap-disj
d_slot'45'heap'45'disj_1104 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_slot'45'heap'45'disj_1104 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.block-run-exec
d_block'45'run'45'exec_1130 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_block'45'run'45'exec_1130 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.event-of
d_event'45'of_1360 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_event'45'of_1360 ~v0 ~v1 ~v2 ~v3 = du_event'45'of_1360
du_event'45'of_1360 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_event'45'of_1360
  = coe MAlonzo.Code.Once.Adequacy.FlatEvents.du_event'45'of_280
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.flat-events
d_flat'45'events_1362 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'events_1362 ~v0 v1 ~v2 ~v3 = du_flat'45'events_1362 v1
du_flat'45'events_1362 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_flat'45'events_1362 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_286 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.flat-events-fetch
d_flat'45'events'45'fetch_1364 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'events'45'fetch_1364 ~v0 v1 ~v2 ~v3
  = du_flat'45'events'45'fetch_1364 v1
du_flat'45'events'45'fetch_1364 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_flat'45'events'45'fetch_1364 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events'45'fetch_290
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.flat-events-step
d_flat'45'events'45'step_1368 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'events'45'step_1368 ~v0 v1 ~v2 ~v3
  = du_flat'45'events'45'step_1368 v1
du_flat'45'events'45'step_1368 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_flat'45'events'45'step_1368 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events'45'step_288
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.fetch-nothing-drop
d_fetch'45'nothing'45'drop_1374 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'nothing'45'drop_1374 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.fetch-just-drop
d_fetch'45'just'45'drop_1398 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'just'45'drop_1398 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.sigop-concrete-fetch
d_sigop'45'concrete'45'fetch_1438 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'concrete'45'fetch_1438 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.sigop-run-arith
d_sigop'45'run'45'arith_1478 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'run'45'arith_1478 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.execInstr-cmp-mi
d_execInstr'45'cmp'45'mi_1512 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Mem_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_execInstr'45'cmp'45'mi_1512 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.event-of-pure
d_event'45'of'45'pure_1536 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_event'45'of'45'pure_1536 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.store-guard
d_store'45'guard_1552 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'guard_1552 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go
d_go_1564 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_1564 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.slot-empty-stop
d_slot'45'empty'45'stop_1632 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_slot'45'empty'45'stop_1632 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                             ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21
  = du_slot'45'empty'45'stop_1632
du_slot'45'empty'45'stop_1632 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_slot'45'empty'45'stop_1632
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
      erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.dc
d_dc_1674 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_1674 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21
  = du_dc_1674 v14
du_dc_1674 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_1674 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.d_dataCorr_524
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.halt-s
d_halt'45's_1676 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_1676 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.fetch-x86
d_fetch'45'x86_1678 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_1678 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.rd
d_rd_1682 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rd_1682 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.stuck
d_stuck_1684 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stuck_1684 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.result
d_result_1690 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result_1690 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.sigop-run-external
d_sigop'45'run'45'external_1716 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'run'45'external_1716 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.events-running-end
d_events'45'running'45'end_1756 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_events'45'running'45'end_1756 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
  = du_events'45'running'45'end_1756
du_events'45'running'45'end_1756 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_events'45'running'45'end_1756
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
      erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.cfetch-nothing
d_cfetch'45'nothing_1784 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cfetch'45'nothing_1784 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.events-running-call
d_events'45'running'45'call_1806
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.events-running-call"
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.events-running-thunk
d_events'45'running'45'thunk_1828
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.events-running-thunk"
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.events-running-ret
d_events'45'running'45'ret_1848
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.events-running-ret"
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.emitted-shape-check
d_emitted'45'shape'45'check_1854
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.emitted-shape-check"
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.run-meets
d_run'45'meets_1862
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.run-meets"
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.arith-sigop-contract
d_arith'45'sigop'45'contract_1882
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.arith-sigop-contract"
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.external-sigop-contract
d_external'45'sigop'45'contract_1902
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.external-sigop-contract"
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.fetch≡lookup
d_fetch'8801'lookup_1908 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'8801'lookup_1908 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.emitted-slot-below-budget
d_emitted'45'slot'45'below'45'budget_1928 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_emitted'45'slot'45'below'45'budget_1928 v0 ~v1 ~v2 ~v3 v4 v5 ~v6
                                          v7 ~v8 ~v9
  = du_emitted'45'slot'45'below'45'budget_1928 v0 v4 v5 v7
du_emitted'45'slot'45'below'45'budget_1928 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_emitted'45'slot'45'below'45'budget_1928 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotBudget.du_emitted'45'slot'45'seg_2272
      (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.ff→seg-id
d_ff'8594'seg'45'id_1944 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ff'8594'seg'45'id_1944 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.RetMatch
d_RetMatch_1950 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_RetMatch_1950
  = C_rm'45''91''93'_1956 | C_rm'45''8759'_1968 T_RetMatch_1950
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.SegWF
d_SegWF_1976 a0 a1 a2 a3 a4 a5 a6 = ()
newtype T_SegWF_1976 = C_mkSegWF_1992 T_RetMatch_1950
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.SegWF.seg-cur
d_seg'45'cur_1988 ::
  T_SegWF_1976 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'cur_1988 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.SegWF.seg-stack
d_seg'45'stack_1990 :: T_SegWF_1976 -> T_RetMatch_1950
d_seg'45'stack_1990 v0
  = case coe v0 of
      C_mkSegWF_1992 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.dj-aux
d_dj'45'aux_2000 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_dj'45'aux_2000 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_dj'45'aux_2000 v4
du_dj'45'aux_2000 ::
  Maybe Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_dj'45'aux_2000 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.db-aux
d_db'45'aux_2018 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_db'45'aux_2018 ~v0 v1 ~v2 ~v3 v4 v5 v6 ~v7
  = du_db'45'aux_2018 v1 v4 v5 v6
du_db'45'aux_2018 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_db'45'aux_2018 v0 v1 v2 v3
  = if coe v1
      then coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                du_dj'45'aux_2000
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v0)
                   (coe v3) (coe v2)))
      else coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.JumpPost
d_JumpPost_2040 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_JumpPost_2040
  = C_jp'45'suc_2050 | C_jp'45'halt_2052 | C_jp'45'to_2056 Integer
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.PcView
d_PcView_2060 a0 a1 a2 a3 a4 = ()
data T_PcView_2060
  = C_pv'45'suc_2068 AgdaAny |
    C_pv'45'jump_2076 AgdaAny MAlonzo.Code.Once.CCC.Label.T_LabelId_6
                      ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
                       T_JumpPost_2040) |
    C_pv'45'thunk_2082 MAlonzo.Code.Once.CCC.Label.T_LabelId_6
                       Integer |
    C_pv'45'ret_2086 Integer
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.pcView
d_pcView_2090 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  AgdaAny -> T_PcView_2060
d_pcView_2090 ~v0 v1 ~v2 ~v3 v4 ~v5 = du_pcView_2090 v1 v4
du_pcView_2090 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  T_PcView_2060
du_pcView_2090 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2194
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2196
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202 v2
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204 v2
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2212 v2
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2218 v2
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2224
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2226 v2
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2228 v2
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2230 v2
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2232 v2
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2238 v2 v3 v4
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2242 v2 v3 v4
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2244 v2
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2246
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2248 v2
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252 v2
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256 v2
        -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258 v2
        -> case coe v2 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176 v3
               -> coe C_pv'45'suc_2068 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178 v3
               -> coe
                    C_pv'45'jump_2076 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) v3
                    (\ v4 v5 -> coe du_go_2106 (coe v0) (coe v3) v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180 v3
               -> coe
                    C_pv'45'jump_2076 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) v3
                    (coe du_go_2138 (coe v0) (coe v3))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182 v3
               -> coe
                    C_pv'45'jump_2076 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) v3
                    (coe du_go_2170 (coe v0) (coe v3))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2184 v3 v4
               -> coe C_pv'45'thunk_2082 v3 v4
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2186 v3
               -> coe C_pv'45'ret_2086 v3
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go
d_go_2106 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_JumpPost_2040
d_go_2106 ~v0 v1 ~v2 ~v3 v4 ~v5 v6 ~v7 = du_go_2106 v1 v4 v6
du_go_2106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_JumpPost_2040
du_go_2106 v0 v1 v2
  = coe
      du_mk_2118
      (coe
         du_dj'45'aux_2000
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v0)
            (coe v2) (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.mk
d_mk_2118 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_JumpPost_2040
d_mk_2118 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_mk_2118 v8
du_mk_2118 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_JumpPost_2040
du_mk_2118 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe C_jp'45'halt_2052
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> coe seq (coe v3) (coe C_jp'45'to_2056 v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go
d_go_2138 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_JumpPost_2040
d_go_2138 ~v0 v1 ~v2 ~v3 v4 ~v5 v6 v7 = du_go_2138 v1 v4 v6 v7
du_go_2138 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_JumpPost_2040
du_go_2138 v0 v1 v2 v3
  = coe
      du_mk_2148
      (coe
         du_db'45'aux_2018 (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_94
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                  (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3)))
               (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)))
         (coe v1) (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.mk
d_mk_2148 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_JumpPost_2040
d_mk_2148 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_mk_2148 v8
du_mk_2148 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_JumpPost_2040
du_mk_2148 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe C_jp'45'suc_2050
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
               -> coe C_jp'45'halt_2052
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                      -> coe seq (coe v4) (coe C_jp'45'to_2056 v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go
d_go_2170 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_JumpPost_2040
d_go_2170 ~v0 v1 ~v2 ~v3 v4 ~v5 v6 v7 = du_go_2170 v1 v4 v6 v7
du_go_2170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_JumpPost_2040
du_go_2170 v0 v1 v2 v3
  = coe
      du_mk_2180
      (coe
         du_db'45'aux_2018 (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_96
            (coe
               MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_108
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))))
         (coe v1) (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.mk
d_mk_2180 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_JumpPost_2040
d_mk_2180 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_mk_2180 v8
du_mk_2180 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_JumpPost_2040
du_mk_2180 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe C_jp'45'suc_2050
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
               -> coe C_jp'45'halt_2052
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                      -> coe seq (coe v4) (coe C_jp'45'to_2056 v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.run-seg-wf
d_run'45'seg'45'wf_2300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  T_SegWF_1976
d_run'45'seg'45'wf_2300 v0 v1 ~v2 v3 v4 v5 v6
  = du_run'45'seg'45'wf_2300 v0 v1 v3 v4 v5 v6
du_run'45'seg'45'wf_2300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  T_SegWF_1976
du_run'45'seg'45'wf_2300 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_mkRunAt_234 v6 v8 v9
        -> coe
             du_go_2322 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe v8) (coe v9) (coe v9)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.B₀
d_B'8320'_2318 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotBudget.T_SegState_214
d_B'8320'_2318 v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9
  = du_B'8320'_2318 v0 v6
du_B'8320'_2318 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotBudget.T_SegState_214
du_B'8320'_2318 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotBudget.C_mkSeg_224
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_702
         (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go
d_go_2322 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  T_SegWF_1976
d_go_2322 v0 v1 ~v2 v3 v4 v5 v6 ~v7 v8 v9 ~v10 v11
  = du_go_2322 v0 v1 v3 v4 v5 v6 v8 v9 v11
du_go_2322 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  T_SegWF_1976
du_go_2322 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_reach'45'start_194 v10
        -> coe C_mkSegWF_1992 (coe C_rm'45''91''93'_1956)
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_reach'45'step_200 v9 v10 v11
        -> coe
             du_step_2354 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v6) (coe v7) (coe v10) (coe v11)
             (coe du_pcView_2090 (coe v1) (coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.em
d_em_2346 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_em_2346 v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 ~v10 v11 ~v12 ~v13
          ~v14
  = du_em_2346 v0 v6 v7 v8 v11
du_em_2346 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> AgdaAny
du_em_2346 v0 v1 v2 v3 v4
  = coe
      du_frame'45'op'45'absurd_1038 (coe v0) (coe v4)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      (coe v3)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.ih
d_ih_2348 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_SegWF_1976
d_ih_2348 v0 v1 ~v2 v3 v4 v5 v6 ~v7 v8 v9 ~v10 v11 v12 ~v13 ~v14
  = du_ih_2348 v0 v1 v3 v4 v5 v6 v8 v9 v11 v12
du_ih_2348 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  T_SegWF_1976
du_ih_2348 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_go_2322 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v9)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.lk
d_lk_2350 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lk_2350 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.seg-suc
d_seg'45'suc_2352 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'suc_2352 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.step
d_step_2354 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_PcView_2060 -> T_SegWF_1976
d_step_2354 v0 v1 ~v2 v3 v4 v5 v6 ~v7 v8 v9 ~v10 v11 v12 ~v13 ~v14
            v15
  = du_step_2354 v0 v1 v3 v4 v5 v6 v8 v9 v11 v12 v15
du_step_2354 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  T_PcView_2060 -> T_SegWF_1976
du_step_2354 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      C_pv'45'suc_2068 v11
        -> coe
             C_mkSegWF_1992
             (d_seg'45'stack_1990
                (coe
                   du_ih_2348 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                   (coe v6) (coe v7) (coe v8) (coe v9)))
      C_pv'45'jump_2076 v11 v12 v14
        -> coe
             C_mkSegWF_1992
             (d_seg'45'stack_1990
                (coe
                   du_ih_2348 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                   (coe v6) (coe v7) (coe v8) (coe v9)))
      C_pv'45'thunk_2082 v11 v12
        -> coe
             C_mkSegWF_1992
             (d_seg'45'stack_1990
                (coe
                   du_ih_2348 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                   (coe v6) (coe v7) (coe v8) (coe v9)))
      C_pv'45'ret_2086 v11
        -> coe
             du_ret'45'step_2440 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._._.same
d_same_2364 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackSlot.T_SameFrames_310
d_same_2364 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._._.stable
d_stable_2366 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stable_2366 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._._.same
d_same_2382 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   T_JumpPost_2040) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackSlot.T_SameFrames_310
d_same_2382 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._._.lkm
d_lkm_2384 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   T_JumpPost_2040) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lkm_2384 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._._.jgo
d_jgo_2386 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   T_JumpPost_2040) ->
  T_JumpPost_2040 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_jgo_2386 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._._.pc-eq
d_pc'45'eq_2420 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pc'45'eq_2420 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._._.step-eq
d_step'45'eq_2422 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'eq_2422 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._._.ret-step
d_ret'45'step_2440 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_SegWF_1976
d_ret'45'step_2440 v0 v1 ~v2 v3 v4 v5 v6 ~v7 v8 v9 ~v10 v11 v12
                   ~v13 ~v14 ~v15 ~v16 ~v17
  = du_ret'45'step_2440 v0 v1 v3 v4 v5 v6 v8 v9 v11 v12
du_ret'45'step_2440 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  T_SegWF_1976
du_ret'45'step_2440 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_go'45'rm_2450
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v8))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v8)))
      (coe
         d_seg'45'stack_1990
         (coe
            du_ih_2348 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v6) (coe v7) (coe v8) (coe v9)))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._._._.go-rm
d_go'45'rm_2450 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [Integer] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_RetMatch_1950 -> T_SegWF_1976
d_go'45'rm_2450 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 ~v13 ~v14 ~v15 v16 v17 ~v18 ~v19 v20
  = du_go'45'rm_2450 v16 v17 v20
du_go'45'rm_2450 ::
  [Integer] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_RetMatch_1950 -> T_SegWF_1976
du_go'45'rm_2450 v0 v1 v2
  = case coe v0 of
      []
        -> coe
             seq (coe v1)
             (coe seq (coe v2) (coe C_mkSegWF_1992 (coe C_rm'45''91''93'_1956)))
      (:) v3 v4
        -> case coe v1 of
             (:) v5 v6
               -> coe
                    seq (coe v5)
                    (case coe v2 of
                       C_rm'45''8759'_1968 v13 -> coe C_mkSegWF_1992 v13
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.stack-ptr-step
d_stack'45'ptr'45'step_2502 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_320 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_320
d_stack'45'ptr'45'step_2502 ~v0 v1 ~v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 v10
  = du_stack'45'ptr'45'step_2502 v1 v4 v5 v6 v10
du_stack'45'ptr'45'step_2502 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_320 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_320
du_stack'45'ptr'45'step_2502 v0 v1 v2 v3 v4
  = coe
      seq (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.du_flat'45'stack'45'ptr_1564
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.entry-stack-ptr
d_entry'45'stack'45'ptr_2934 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_320
d_entry'45'stack'45'ptr_2934 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_entry'45'stack'45'ptr_2934 v4 v5
du_entry'45'stack'45'ptr_2934 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_320
du_entry'45'stack'45'ptr_2934 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                    -> case coe v11 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                           -> case coe v13 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                  -> coe
                                                       seq (coe v15)
                                                       (coe
                                                          MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.C_mkStackPtrWF_352
                                                          (coe
                                                             (\ v16 ->
                                                                coe
                                                                  du_go_2952
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74
                                                                           (coe v0)))
                                                                     (coe v16))))
                                                          (coe
                                                             (\ v16 ->
                                                                coe
                                                                  MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                          (coe
                                                             (\ v16 v17 ->
                                                                coe
                                                                  MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go
d_go_2952 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_go_2952 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 v15 ~v16
  = du_go_2952 v15
du_go_2952 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
du_go_2952 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v1
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.entry-ptr-bounds
d_entry'45'ptr'45'bounds_3002 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_360
d_entry'45'ptr'45'bounds_3002 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_entry'45'ptr'45'bounds_3002 v4 v5
du_entry'45'ptr'45'bounds_3002 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_360
du_entry'45'ptr'45'bounds_3002 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                    -> case coe v11 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                           -> case coe v13 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                  -> coe
                                                       seq (coe v15)
                                                       (coe
                                                          MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.C_mkPtrBounds_394
                                                          (coe
                                                             (\ v16 ->
                                                                coe
                                                                  du_go_3020
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74
                                                                           (coe v0)))
                                                                     (coe v16))))
                                                          (coe
                                                             (\ v16 ->
                                                                coe
                                                                  MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                          (coe
                                                             (\ v16 v17 ->
                                                                coe
                                                                  MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go
d_go_3020 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_go_3020 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 v15 ~v16
  = du_go_3020 v15
du_go_3020 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
du_go_3020 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v1
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.entry-flat-wf
d_entry'45'flat'45'wf_3070 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506
d_entry'45'flat'45'wf_3070 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_entry'45'flat'45'wf_3070 v4 v5
du_entry'45'flat'45'wf_3070 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506
du_entry'45'flat'45'wf_3070 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                    -> case coe v11 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                           -> case coe v13 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                  -> coe
                                                       seq (coe v15)
                                                       (coe
                                                          MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.C_constructor_548
                                                          (\ v16 ->
                                                             coe
                                                               du_go_3088
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74
                                                                        (coe v0)))
                                                                  (coe v16)))
                                                          (\ v16 ->
                                                             coe
                                                               MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                          (\ v16 v17 ->
                                                             coe
                                                               MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go
d_go_3088 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_go_3088 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 v15 ~v16
  = du_go_3088 v15
du_go_3088 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
du_go_3088 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v1
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.run-stack-ptr
d_run'45'stack'45'ptr_3146 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_320
d_run'45'stack'45'ptr_3146 ~v0 v1 ~v2 ~v3 v4 v5 v6
  = du_run'45'stack'45'ptr_3146 v1 v4 v5 v6
du_run'45'stack'45'ptr_3146 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_320
du_run'45'stack'45'ptr_3146 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_mkRunAt_234 v4 v6 v7
        -> coe du_go_3166 (coe v0) (coe v1) (coe v2) (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go
d_go_3166 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_320
d_go_3166 ~v0 v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
  = du_go_3166 v1 v4 v10 v11
du_go_3166 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_320
du_go_3166 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_reach'45'start_194 v5
        -> coe du_entry'45'stack'45'ptr_2934 (coe v2) (coe v5)
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_reach'45'step_200 v4 v5 v6
        -> coe
             du_stack'45'ptr'45'step_2502 (coe v0) (coe v4) (coe v1) (coe v5)
             (coe du_go_3166 (coe v0) (coe v1) (coe v5) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.stack-ptr-current
d_stack'45'ptr'45'current_3190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'ptr'45'current_3190 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9
  = du_stack'45'ptr'45'current_3190
du_stack'45'ptr'45'current_3190 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stack'45'ptr'45'current_3190
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.stack-ptr-current-suc
d_stack'45'ptr'45'current'45'suc_3212 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'ptr'45'current'45'suc_3212 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      ~v7 ~v8 ~v9
  = du_stack'45'ptr'45'current'45'suc_3212
du_stack'45'ptr'45'current'45'suc_3212 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stack'45'ptr'45'current'45'suc_3212
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.slot-read-in-frame
d_slot'45'read'45'in'45'frame_3234 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'read'45'in'45'frame_3234 v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 v8
                                   ~v9 ~v10
  = du_slot'45'read'45'in'45'frame_3234 v0 v5 v6 v8
du_slot'45'read'45'in'45'frame_3234 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'read'45'in'45'frame_3234 v0 v1 v2 v3
  = coe
      du_emitted'45'slot'45'below'45'budget_1928 (coe v0)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'ir_226
         (coe v3))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v1)) (coe v2)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.emitted-alloc-min
d_emitted'45'alloc'45'min_3262 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_emitted'45'alloc'45'min_3262 v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8
  = du_emitted'45'alloc'45'min_3262 v0 v5 v7
du_emitted'45'alloc'45'min_3262 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_emitted'45'alloc'45'min_3262 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.AllocMin.du_fetch'45'alloc'45'min_686
             v0 (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
             (coe MAlonzo.Code.Once.IRTy.C_Unit_16) v3
             (MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v1)) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.ptr-bounds-step
d_ptr'45'bounds'45'step_3278 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_360 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_360
d_ptr'45'bounds'45'step_3278 v0 v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9 v10
                             v11
  = du_ptr'45'bounds'45'step_3278 v0 v1 v4 v5 v6 v7 v9 v10 v11
du_ptr'45'bounds'45'step_3278 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_360 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_360
du_ptr'45'bounds'45'step_3278 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2194
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2196
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2210 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2212 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2218 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2224
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2226 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2228 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2230 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2232 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2238 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v12 v13 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2242 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v12 v13 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2244 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2246
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2248 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe
                (\ v10 v11 ->
                   coe
                     du_emitted'45'alloc'45'min_3262 (coe v0) (coe v4)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'ir_226
                           (coe v5))
                        erased)))
             (coe v7) (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.run-wf-ptr-bounds
d_run'45'wf'45'ptr'45'bounds_3836 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'wf'45'ptr'45'bounds_3836 v0 v1 ~v2 ~v3 v4 v5 v6
  = du_run'45'wf'45'ptr'45'bounds_3836 v0 v1 v4 v5 v6
du_run'45'wf'45'ptr'45'bounds_3836 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'wf'45'ptr'45'bounds_3836 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_mkRunAt_234 v5 v7 v8
        -> coe
             du_go_3856 (coe v0) (coe v1) (coe v2) (coe v5) erased (coe v7)
             (coe v3) (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go
d_go_3856 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_3856 v0 v1 ~v2 ~v3 v4 ~v5 v6 v7 v8 ~v9 v10 v11
  = du_go_3856 v0 v1 v4 v6 v7 v8 v10 v11
du_go_3856 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_186 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_3856 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_reach'45'start_194 v9
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_entry'45'flat'45'wf_3070 (coe v6) (coe v9))
             (coe du_entry'45'ptr'45'bounds_3002 (coe v6) (coe v9))
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_reach'45'step_200 v8 v9 v10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_flat'45'wf'45'step_2064
                (coe v1) (coe v8) (coe v2) (coe v9)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_go_3856 (coe v0) (coe v1) (coe v2) (coe v3) erased (coe v5)
                      (coe v9) (coe v10))))
             (coe
                du_ptr'45'bounds'45'step_3278 (coe v0) (coe v1) (coe v8) (coe v2)
                (coe v9)
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_mkRunAt_234
                   v3 v5 v10)
                (coe
                   du_frame'45'op'45'absurd_1038 (coe v0) (coe v9)
                   (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v4))
                   (coe v5))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_go_3856 (coe v0) (coe v1) (coe v2) (coe v3) erased (coe v5)
                      (coe v9) (coe v10)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      du_go_3856 (coe v0) (coe v1) (coe v2) (coe v3) erased (coe v5)
                      (coe v9) (coe v10))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.run-ptr-bounds
d_run'45'ptr'45'bounds_3880 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_360
d_run'45'ptr'45'bounds_3880 v0 v1 ~v2 ~v3 v4 v5 v6
  = du_run'45'ptr'45'bounds_3880 v0 v1 v4 v5 v6
du_run'45'ptr'45'bounds_3880 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_360
du_run'45'ptr'45'bounds_3880 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         du_run'45'wf'45'ptr'45'bounds_3836 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.run-shape-check
d_run'45'shape'45'check_3896 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'shape'45'check_3896 v0 v1 ~v2 v3 ~v4 ~v5 v6
  = du_run'45'shape'45'check_3896 v0 v1 v3 v6
du_run'45'shape'45'check_3896 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'shape'45'check_3896 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe du_chk_3908 (coe v0) (coe v1) (coe v2) (coe v3)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe du_chk_3908 (coe v0) (coe v1) (coe v2) (coe v3)))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.chk
d_chk_3908 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_chk_3908 v0 v1 ~v2 v3 ~v4 ~v5 v6 = du_chk_3908 v0 v1 v3 v6
du_chk_3908 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_chk_3908 v0 v1 v2 v3
  = coe
      d_emitted'45'shape'45'check_1854 v0 v1 erased v2
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'ir_226
         (coe v3))
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'heap_230
         (coe v3))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.load-indirect-target-ptr
d_load'45'indirect'45'target'45'ptr_3918 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'target'45'ptr_3918 v0 v1 ~v2 v3 v4 v5 v6 ~v7
  = du_load'45'indirect'45'target'45'ptr_3918 v0 v1 v3 v4 v5 v6
du_load'45'indirect'45'target'45'ptr_3918 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'target'45'ptr_3918 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.du_site'45'load'45'ptr_2284
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_e'45'in1_34
         (coe
            du_st_3938 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v4)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_run'45'meets_1862 v0 v1 erased v2 v3 v4 v5
            (coe du_env_3934 (coe v0) (coe v1) (coe v2) (coe v5)) erased))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.sc
d_sc_3932 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sc_3932 v0 v1 ~v2 v3 ~v4 ~v5 v6 ~v7 = du_sc_3932 v0 v1 v3 v6
du_sc_3932 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sc_3932 v0 v1 v2 v3
  = coe
      du_run'45'shape'45'check_3896 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.env
d_env_3934 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
d_env_3934 v0 v1 ~v2 v3 ~v4 ~v5 v6 ~v7 = du_env_3934 v0 v1 v3 v6
du_env_3934 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
du_env_3934 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_sc_3932 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.chk
d_chk_3936 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chk_3936 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.st
d_st_3938 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
d_st_3938 v0 v1 ~v2 v3 v4 v5 v6 ~v7 = du_st_3938 v0 v1 v3 v4 v5 v6
du_st_3938 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
du_st_3938 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_state'45'at_980
      (coe du_env_3934 (coe v0) (coe v1) (coe v2) (coe v5))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_entry'45'expect_962
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
      (coe v3) (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v4))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.ok
d_ok_3940 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok_3940 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.load-indirect-suc-target-ptr
d_load'45'indirect'45'suc'45'target'45'ptr_3948 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'target'45'ptr_3948 v0 v1 ~v2 v3 v4 v5
                                                v6 ~v7
  = du_load'45'indirect'45'suc'45'target'45'ptr_3948
      v0 v1 v3 v4 v5 v6
du_load'45'indirect'45'suc'45'target'45'ptr_3948 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'target'45'ptr_3948 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.du_site'45'load'45'ptr_2284
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_e'45'in1_34
         (coe
            du_st_3968 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v4)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_run'45'meets_1862 v0 v1 erased v2 v3 v4 v5
            (coe du_env_3964 (coe v0) (coe v1) (coe v2) (coe v5)) erased))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.sc
d_sc_3962 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sc_3962 v0 v1 ~v2 v3 ~v4 ~v5 v6 ~v7 = du_sc_3962 v0 v1 v3 v6
du_sc_3962 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sc_3962 v0 v1 v2 v3
  = coe
      du_run'45'shape'45'check_3896 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.env
d_env_3964 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
d_env_3964 v0 v1 ~v2 v3 ~v4 ~v5 v6 ~v7 = du_env_3964 v0 v1 v3 v6
du_env_3964 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
du_env_3964 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_sc_3962 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.chk
d_chk_3966 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chk_3966 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.st
d_st_3968 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
d_st_3968 v0 v1 ~v2 v3 v4 v5 v6 ~v7 = du_st_3968 v0 v1 v3 v4 v5 v6
du_st_3968 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
du_st_3968 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_state'45'at_980
      (coe du_env_3964 (coe v0) (coe v1) (coe v2) (coe v5))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_entry'45'expect_962
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
      (coe v3) (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v4))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.ok
d_ok_3970 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok_3970 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.store-indirect-target-ptr
d_store'45'indirect'45'target'45'ptr_3978 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_store'45'indirect'45'target'45'ptr_3978 v0 v1 ~v2 v3 v4 v5 v6 ~v7
  = du_store'45'indirect'45'target'45'ptr_3978 v0 v1 v3 v4 v5 v6
du_store'45'indirect'45'target'45'ptr_3978 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_store'45'indirect'45'target'45'ptr_3978 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.du_site'45'store'45'ptr_3060
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_e'45'in1_34
         (coe
            du_st_3998 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v4)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_run'45'meets_1862 v0 v1 erased v2 v3 v4 v5
            (coe du_env_3994 (coe v0) (coe v1) (coe v2) (coe v5)) erased))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.sc
d_sc_3992 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sc_3992 v0 v1 ~v2 v3 ~v4 ~v5 v6 ~v7 = du_sc_3992 v0 v1 v3 v6
du_sc_3992 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sc_3992 v0 v1 v2 v3
  = coe
      du_run'45'shape'45'check_3896 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.env
d_env_3994 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
d_env_3994 v0 v1 ~v2 v3 ~v4 ~v5 v6 ~v7 = du_env_3994 v0 v1 v3 v6
du_env_3994 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
du_env_3994 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_sc_3992 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.chk
d_chk_3996 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chk_3996 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.st
d_st_3998 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
d_st_3998 v0 v1 ~v2 v3 v4 v5 v6 ~v7 = du_st_3998 v0 v1 v3 v4 v5 v6
du_st_3998 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
du_st_3998 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_state'45'at_980
      (coe du_env_3994 (coe v0) (coe v1) (coe v2) (coe v5))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_entry'45'expect_962
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
      (coe v3) (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v4))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.ok
d_ok_4000 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok_4000 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.store-indirect-suc-target-ptr
d_store'45'indirect'45'suc'45'target'45'ptr_4008 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_store'45'indirect'45'suc'45'target'45'ptr_4008 v0 v1 ~v2 v3 v4 v5
                                                 v6 ~v7
  = du_store'45'indirect'45'suc'45'target'45'ptr_4008
      v0 v1 v3 v4 v5 v6
du_store'45'indirect'45'suc'45'target'45'ptr_4008 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_store'45'indirect'45'suc'45'target'45'ptr_4008 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.du_site'45'store'45'ptr_3060
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_e'45'in1_34
         (coe
            du_st_4028 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v4)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_run'45'meets_1862 v0 v1 erased v2 v3 v4 v5
            (coe du_env_4024 (coe v0) (coe v1) (coe v2) (coe v5)) erased))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.sc
d_sc_4022 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sc_4022 v0 v1 ~v2 v3 ~v4 ~v5 v6 ~v7 = du_sc_4022 v0 v1 v3 v6
du_sc_4022 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sc_4022 v0 v1 v2 v3
  = coe
      du_run'45'shape'45'check_3896 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.env
d_env_4024 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
d_env_4024 v0 v1 ~v2 v3 ~v4 ~v5 v6 ~v7 = du_env_4024 v0 v1 v3 v6
du_env_4024 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
du_env_4024 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_sc_4022 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.chk
d_chk_4026 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chk_4026 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.st
d_st_4028 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
d_st_4028 v0 v1 ~v2 v3 v4 v5 v6 ~v7 = du_st_4028 v0 v1 v3 v4 v5 v6
du_st_4028 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
du_st_4028 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_state'45'at_980
      (coe du_env_4024 (coe v0) (coe v1) (coe v2) (coe v5))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_entry'45'expect_962
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
      (coe v3) (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v4))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.ok
d_ok_4030 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok_4030 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.store-nonptr-absurd
d_store'45'nonptr'45'absurd_4040 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_store'45'nonptr'45'absurd_4040 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.wits
d_wits_4058 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wits_4058 v0 v1 ~v2 v3 v4 v5 ~v6 v7 ~v8 ~v9 ~v10
  = du_wits_4058 v0 v1 v3 v4 v5 v7
du_wits_4058 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wits_4058 v0 v1 v2 v3 v4 v5
  = coe
      du_store'45'indirect'45'target'45'ptr_3978 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.store-suc-nonptr-absurd
d_store'45'suc'45'nonptr'45'absurd_4068 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_store'45'suc'45'nonptr'45'absurd_4068 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.wits
d_wits_4086 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wits_4086 v0 v1 ~v2 v3 v4 v5 ~v6 v7 ~v8 ~v9 ~v10
  = du_wits_4086 v0 v1 v3 v4 v5 v7
du_wits_4086 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wits_4086 v0 v1 v2 v3 v4 v5
  = coe
      du_store'45'indirect'45'suc'45'target'45'ptr_4008 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.branch-tag-scrutinee-wf
d_branch'45'tag'45'scrutinee'45'wf_4098 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_branch'45'tag'45'scrutinee'45'wf_4098 v0 v1 ~v2 v3 v4 v5 ~v6 v7
                                        ~v8
  = du_branch'45'tag'45'scrutinee'45'wf_4098 v0 v1 v3 v4 v5 v7
du_branch'45'tag'45'scrutinee'45'wf_4098 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_branch'45'tag'45'scrutinee'45'wf_4098 v0 v1 v2 v3 v4 v5
  = coe
      du_repack_4132
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.du_site'45'branch'45'tag_2432
         (coe
            MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_e'45'in1_34
            (coe
               du_st_4120 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v4)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               d_run'45'meets_1862 v0 v1 erased v2 v3 v4 v5
               (coe du_env_4116 (coe v0) (coe v1) (coe v2) (coe v5)) erased)))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.sc
d_sc_4114 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sc_4114 v0 v1 ~v2 v3 ~v4 ~v5 ~v6 v7 ~v8 = du_sc_4114 v0 v1 v3 v7
du_sc_4114 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sc_4114 v0 v1 v2 v3
  = coe
      du_run'45'shape'45'check_3896 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.env
d_env_4116 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
d_env_4116 v0 v1 ~v2 v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_env_4116 v0 v1 v3 v7
du_env_4116 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
du_env_4116 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_sc_4114 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.chk
d_chk_4118 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chk_4118 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.st
d_st_4120 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
d_st_4120 v0 v1 ~v2 v3 v4 v5 ~v6 v7 ~v8
  = du_st_4120 v0 v1 v3 v4 v5 v7
du_st_4120 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
du_st_4120 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_state'45'at_980
      (coe du_env_4116 (coe v0) (coe v1) (coe v2) (coe v5))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_entry'45'expect_962
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
      (coe v3) (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v4))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.ok
d_ok_4122 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok_4122 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.repack
d_repack_4132 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_repack_4132 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_repack_4132 v9
du_repack_4132 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_repack_4132 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v6)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.store-indirect-inbounds
d_store'45'indirect'45'inbounds_4148 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_store'45'indirect'45'inbounds_4148 v0 v1 ~v2 ~v3 v4 v5 v6 v7 ~v8
                                     ~v9
  = du_store'45'indirect'45'inbounds_4148 v0 v1 v4 v5 v6 v7
du_store'45'indirect'45'inbounds_4148 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_store'45'indirect'45'inbounds_4148 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.du_ptr'45'bounds'45'cell_424
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v4)
      (coe
         du_run'45'ptr'45'bounds_3880 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v5))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.store-indirect-suc-inbounds
d_store'45'indirect'45'suc'45'inbounds_4168 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_store'45'indirect'45'suc'45'inbounds_4168 v0 v1 ~v2 ~v3 v4 v5 ~v6
                                            v7 ~v8 ~v9
  = du_store'45'indirect'45'suc'45'inbounds_4168 v0 v1 v4 v5 v7
du_store'45'indirect'45'suc'45'inbounds_4168 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_store'45'indirect'45'suc'45'inbounds_4168 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.du_ptr'45'bounds'45'suc_406
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
      (coe
         du_run'45'ptr'45'bounds_3880 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.load-indirect-target-wf
d_load'45'indirect'45'target'45'wf_4190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'target'45'wf_4190 v0 v1 ~v2 v3 v4 v5 v6 ~v7
  = du_load'45'indirect'45'target'45'wf_4190 v0 v1 v3 v4 v5 v6
du_load'45'indirect'45'target'45'wf_4190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'target'45'wf_4190 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.CCC.Codegen.ShapeTable.du_site'45'load'45'ptr_2284
              (coe
                 MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_e'45'in1_34
                 (coe
                    MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_state'45'at_980
                    (coe du_env_3934 (coe v0) (coe v1) (coe v2) (coe v5))
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_entry'45'expect_962
                       (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
                    (coe v3)
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v4))))
              (coe
                 MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                 (coe
                    MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v4)))
                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    d_run'45'meets_1862 v0 v1 erased v2 v3 v4 v5
                    (coe du_env_3934 (coe v0) (coe v1) (coe v2) (coe v5)) erased)) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                   (coe
                      (\ v9 v10 ->
                         coe
                           MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.du_ptr'45'bounds'45'cell_424
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v9)
                           (coe
                              du_run'45'ptr'45'bounds_3880 (coe v0) (coe v1) (coe v3) (coe v4)
                              (coe v5)))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.load-indirect-suc-target-wf
d_load'45'indirect'45'suc'45'target'45'wf_4228 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'target'45'wf_4228 v0 v1 ~v2 v3 v4 v5
                                               v6 ~v7
  = du_load'45'indirect'45'suc'45'target'45'wf_4228 v0 v1 v3 v4 v5 v6
du_load'45'indirect'45'suc'45'target'45'wf_4228 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'target'45'wf_4228 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.CCC.Codegen.ShapeTable.du_site'45'load'45'ptr_2284
              (coe
                 MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_e'45'in1_34
                 (coe
                    MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_state'45'at_980
                    (coe du_env_3964 (coe v0) (coe v1) (coe v2) (coe v5))
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_entry'45'expect_962
                       (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
                    (coe v3)
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v4))))
              (coe
                 MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                 (coe
                    MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v4)))
                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    d_run'45'meets_1862 v0 v1 erased v2 v3 v4 v5
                    (coe du_env_3964 (coe v0) (coe v1) (coe v2) (coe v5)) erased)) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                   (coe
                      (\ v9 v10 ->
                         coe
                           MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.du_ptr'45'bounds'45'suc_406
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
                           (coe
                              du_run'45'ptr'45'bounds_3880 (coe v0) (coe v1) (coe v3) (coe v4)
                              (coe v5)))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.events-agree
d_events'45'agree_4274 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_events'45'agree_4274 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = du_events'45'agree_4274 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_events'45'agree_4274 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_events'45'agree_4274 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v4 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             erased
      _ -> let v12 = subInt (coe v4) (coe (1 :: Integer)) in
           coe
             (coe
                du_go'45'h_4652 (coe v0) (coe v1) (coe v2) (coe v3) (coe v12)
                (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v8))))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.events-running
d_events'45'running_4292 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_events'45'running_4292 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                         ~v13
  = du_events'45'running_4292 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_events'45'running_4292 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_events'45'running_4292 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_go_4686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_216 (coe v7)
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v8)))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.events-running-fetch
d_events'45'running'45'fetch_4312 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_events'45'running'45'fetch_4312 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9
                                  v10 v11 v12 v13 ~v14 v15
  = du_events'45'running'45'fetch_4312
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v15
du_events'45'running'45'fetch_4312 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_events'45'running'45'fetch_4312 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                   v10 v11 v12 v13
  = case coe v10 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190
        -> coe
             du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'mov'45'to'45'output_688
                (coe v9) (coe v11))
             (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192
        -> coe
             du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'mov'45'to'45'input_712
                (coe v9) (coe v11))
             (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2194
        -> coe
             du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'mov'45'output'45'to'45'input2_760
                (coe v9) (coe v11))
             (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2196
        -> coe
             du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'mov'45'input2'45'to'45'output_736
                (coe v9) (coe v11))
             (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198
        -> coe
             du_load'45'indirect'45'step_4446 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
             (coe v11) (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200
        -> coe
             du_load'45'indirect'45'suc'45'step_4464 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
             (coe v11) (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202 v14
        -> coe
             du_load'45'from'45'slot'45'step_4484 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
             (coe v14) (coe v11) (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204 v14
        -> coe
             du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'store'45'at'45'slot_2036
                (coe v8) (coe v9) (coe v14) (coe v11))
             (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206
        -> coe
             du_store'45'indirect'45'step_4542 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
             (coe v11) (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208
        -> coe
             du_store'45'indirect'45'suc'45'step_4560 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
             (coe v11) (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2210 v14
        -> coe
             du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'lea'45'slot_2910
                (coe v9) (coe v14) (coe v11))
             (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2212 v14
        -> coe
             du_restore'45'input'45'step_4504 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
             (coe v14) (coe v11) (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2214 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2216 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2218 v14
        -> coe
             du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'reclaim'45'to_1104
                (coe v9) (coe v11))
             (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2220 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2222
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2224
        -> coe
             d_events'45'running'45'call_1806 v0 v1 erased v2 v3 v4 v5 v6 v7 v8
             v9 v11 v12 erased erased
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2226 v14
        -> coe
             du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'worklist'45'init_1036
                (coe v9) (coe v11))
             (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2228 v14
        -> coe
             du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'worklist'45'push_1782
                (coe v8) (coe v9) (coe v14) (coe v11))
             (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2230 v14
        -> coe
             du_worklist'45'pop'45'step_4524 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v14)
             (coe v11) (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2232 v14
        -> coe
             du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'worklist'45'check_1070
                (coe v9) (coe v11))
             (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2238 v14 v15 v16
        -> coe
             du_sigop'45'step_4584 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v14) (coe v15)
             (coe v16) (coe v11) (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2242 v14 v15 v16
        -> case coe v15 of
             MAlonzo.Code.Once.Type.C_fits'45'int_198
               -> coe
                    du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2242
                       (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v15) (coe v16))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'const_1584
                       (coe v9) (coe v16) (coe v11))
                    (coe v12)
             MAlonzo.Code.Once.Type.C_fits'45'float_200
               -> coe
                    du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2242
                       (coe MAlonzo.Code.Once.Type.C_Float_138) (coe v15) (coe v16))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'const'45'float_1634
                       (coe v9) (coe v16) (coe v11))
                    (coe v12)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2244 v14
        -> coe
             du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'code'45'addr_1684
                (coe v9) (coe v14) (coe v11))
             (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2246
        -> coe
             du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'save'45'closure'45'reg_1732
                (coe v9) (coe v11))
             (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2248 v14
        -> coe
             du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'tag'45'lit_862
                (coe v9) (coe v14) (coe v11))
             (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2250 v14 v15
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252 v14
        -> coe
             du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_extend'45'view_2342
                (coe v3)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v8)))
                (coe v14)
                (coe v2 v3 v7 v8 v9 v14 (d_inv'45'run_1026 (coe v12)) v11 v13))
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'alloc'45'heap_2834
                (coe v8) (coe v9) (coe v14) (coe v11))
             (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2254 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256 v14
        -> case coe v14 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_450
               -> coe
                    du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'scratch'45'one_888
                       (coe v9) (coe v11))
                    (coe v12)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_452
               -> coe
                    du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'scratch'45'zero_912
                       (coe v9) (coe v11))
                    (coe v12)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_454
               -> coe
                    du_scratch'45'dec'45'step_4410 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v11)
                    (coe v12)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_456
               -> coe
                    du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'scratch'45'load'45'count_960
                       (coe v9) (coe v11))
                    (coe v12)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_458
               -> coe
                    du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'count'45'zero_936
                       (coe v9) (coe v11))
                    (coe v12)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_460
               -> coe
                    du_count'45'inc'45'step_4428 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v11)
                    (coe v12)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258 v14
        -> case coe v14 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176 v15
               -> coe
                    du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'label_986
                       (coe v9) (coe v11))
                    (coe v12)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178 v15
               -> coe
                    du_cjmp'45'step_4352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v15) (coe v11)
                    (coe v12)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180 v15
               -> coe
                    du_branch'45'step_4372 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v15) (coe v11)
                    (coe v12)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182 v15
               -> coe
                    du_tag'45'branch'45'step_4392 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v15)
                    (coe v11) (coe v12)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2184 v15 v16
               -> coe
                    d_events'45'running'45'thunk_1828 v0 v1 erased v2 v3 v4 v5 v6 v7 v8
                    v9 v15 v16 v11 v12 erased erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2186 v15
               -> coe
                    d_events'45'running'45'ret_1848 v0 v1 erased v2 v3 v4 v5 v6 v7 v8
                    v9 v15 v11 v12 erased erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2260 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.ccc-step-bs
d_ccc'45'step'45'bs_4332 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ccc'45'step'45'bs_4332 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 ~v10 v11
                         v12 v13 ~v14 ~v15 ~v16 ~v17
  = du_ccc'45'step'45'bs_4332 v0 v1 v3 v4 v5 v6 v7 v8 v9 v11 v12 v13
du_ccc'45'step'45'bs_4332 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ccc'45'step'45'bs_4332 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatComposition.du_x86'45'len_156
            (coe v9))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               du_rec_5758 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11))))
      erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.cjmp-step
d_cjmp'45'step_4352 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cjmp'45'step_4352 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    ~v14 ~v15
  = du_cjmp'45'step_4352 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_cjmp'45'step_4352 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cjmp'45'step_4352 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_go'45'fl_5798 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v1)
         (coe v7) (coe v10))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.branch-step
d_branch'45'step_4372 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_branch'45'step_4372 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                      v13 ~v14 ~v15
  = du_branch'45'step_4372 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_branch'45'step_4372 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_branch'45'step_4372 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_go'45'sv_5982 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v8)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.tag-branch-step
d_tag'45'branch'45'step_4392 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tag'45'branch'45'step_4392 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12 v13 ~v14 ~v15
  = du_tag'45'branch'45'step_4392
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_tag'45'branch'45'step_4392 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_tag'45'branch'45'step_4392 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                              v12
  = coe
      du_go'45'loc_6184 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_wits_6030 (coe v0) (coe v1) (coe v2) (coe v7) (coe v8)
            (coe v12)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               du_wits_6030 (coe v0) (coe v1) (coe v2) (coe v7) (coe v8)
               (coe v12))))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.scratch-dec-step
d_scratch'45'dec'45'step_4410 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_scratch'45'dec'45'step_4410 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10
                              v11 v12 ~v13 ~v14
  = du_scratch'45'dec'45'step_4410
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_scratch'45'dec'45'step_4410 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_scratch'45'dec'45'step_4410 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                               v11
  = coe
      du_go'45'sv_6266 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v8)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.count-inc-step
d_count'45'inc'45'step_4428 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_count'45'inc'45'step_4428 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12 ~v13 ~v14
  = du_count'45'inc'45'step_4428
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_count'45'inc'45'step_4428 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_count'45'inc'45'step_4428 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_go'45'sv_6316 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v8)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.load-indirect-step
d_load'45'indirect'45'step_4446 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'step_4446 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10
                                v11 v12 ~v13 ~v14
  = du_load'45'indirect'45'step_4446
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_load'45'indirect'45'step_4446 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'step_4446 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                 v11
  = coe
      du_go'45'loc_6508 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_wits_6362 (coe v0) (coe v1) (coe v2) (coe v7) (coe v8)
            (coe v11)))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.load-indirect-suc-step
d_load'45'indirect'45'suc'45'step_4464 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'step_4464 v0 v1 ~v2 v3 v4 v5 v6 v7 v8
                                       v9 v10 v11 v12 ~v13 ~v14
  = du_load'45'indirect'45'suc'45'step_4464
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_load'45'indirect'45'suc'45'step_4464 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'step_4464 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11
  = coe
      du_go'45'loc_6696 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_wits_6550 (coe v0) (coe v1) (coe v2) (coe v7) (coe v8)
            (coe v11)))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.load-from-slot-step
d_load'45'from'45'slot'45'step_4484 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'from'45'slot'45'step_4484 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9
                                    v10 v11 v12 v13 ~v14 ~v15
  = du_load'45'from'45'slot'45'step_4484
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_load'45'from'45'slot'45'step_4484 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'from'45'slot'45'step_4484 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                     v10 v11 v12
  = coe
      du_go'45'mem_6744 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
         (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v8))
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v8)))
         v10)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.restore-input-step
d_restore'45'input'45'step_4504 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_restore'45'input'45'step_4504 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10
                                v11 v12 v13 ~v14 ~v15
  = du_restore'45'input'45'step_4504
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_restore'45'input'45'step_4504 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_restore'45'input'45'step_4504 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                 v11 v12
  = coe
      du_go'45'mem_6804 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
         (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v8))
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v8)))
         v10)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.worklist-pop-step
d_worklist'45'pop'45'step_4524 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_worklist'45'pop'45'step_4524 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10
                               v11 v12 v13 ~v14 ~v15
  = du_worklist'45'pop'45'step_4524
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_worklist'45'pop'45'step_4524 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_worklist'45'pop'45'step_4524 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                v11 v12
  = coe
      du_go'45'mem_6864 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
         (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v8))
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v8)))
         v10)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.store-indirect-step
d_store'45'indirect'45'step_4542 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_store'45'indirect'45'step_4542 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10
                                 v11 v12 ~v13 ~v14
  = du_store'45'indirect'45'step_4542
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_store'45'indirect'45'step_4542 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_store'45'indirect'45'step_4542 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                  v11
  = coe
      du_go'45'ptr_6922 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v8)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.store-indirect-suc-step
d_store'45'indirect'45'suc'45'step_4560 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_store'45'indirect'45'suc'45'step_4560 v0 v1 ~v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11 v12 ~v13 ~v14
  = du_store'45'indirect'45'suc'45'step_4560
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_store'45'indirect'45'suc'45'step_4560 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_store'45'indirect'45'suc'45'step_4560 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9 v10 v11
  = coe
      du_go'45'ptr_6996 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v8)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.sigop-step
d_sigop'45'step_4584 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigop'45'step_4584 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                     v14 v15 ~v16 ~v17
  = du_sigop'45'step_4584
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
du_sigop'45'step_4584 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigop'45'step_4584 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                      v14
  = coe
      du_go'45'eff_7076 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12) (coe v13) (coe v14)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_212 (coe v12))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.sigop-external
d_sigop'45'external_4608 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigop'45'external_4608 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                         v13 v14 v15 ~v16 ~v17
  = du_sigop'45'external_4608
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
du_sigop'45'external_4608 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigop'45'external_4608 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                          v13 v14
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               du_rec_7128 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
               (coe v13) (coe v14))))
      erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-h
d_go'45'h_4652 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'h_4652 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 ~v14
  = du_go'45'h_4652 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_go'45'h_4652 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'h_4652 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = if coe v12
      then coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
             erased
      else coe
             du_events'45'running_4292 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go
d_go_4686 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_4686 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13 v14 ~v15
  = du_go_4686 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14
du_go_4686 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_4686 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
        -> coe
             du_events'45'running'45'fetch_4312 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
             (coe v13) (coe v10) (coe v11) erased
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_events'45'running'45'end_1756
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.rec
d_rec_5758 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rec_5758 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 ~v10 v11 v12 v13 ~v14
           ~v15 ~v16 ~v17
  = du_rec_5758 v0 v1 v3 v4 v5 v6 v7 v8 v9 v11 v12 v13
du_rec_5758 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rec_5758 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_events'45'agree_4274 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6) (coe v7)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_570 v1
         v9 v7 v8)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v10))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v10)))
      (coe
         du_flat'45'inv'45'step_1060 (coe v1) (coe v9) (coe v7) (coe v8)
         (coe v11))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.result
d_result_5760 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result_5760 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-fl
d_go'45'fl_5798 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'fl_5798 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 ~v14
                ~v15 v16 ~v17
  = du_go'45'fl_5798 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v16
du_go'45'fl_5798 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'fl_5798 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v13 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
        -> coe
             du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178 (coe v10)))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'jmp_1140
                (coe v7) (coe v9) (coe v14) (coe v11))
             (coe v12)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (2 :: Integer))
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_5808 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_5808 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.halt-s
d_halt'45's_5820 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_5820 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.fetch-x86
d_fetch'45'x86_5822 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_5822 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.s'
d_s''_5824 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_s''_5824 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16
  = du_s''_5824 v10
du_s''_5824 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_s''_5824 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232 (coe v0))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.step-eq
d_step'45'eq_5826 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'eq_5826 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_5832 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_5832 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.result
d_result_5838 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result_5838 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-fl
d_go'45'fl_5874 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'fl_5874 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 ~v14
                ~v15 v16 ~v17 v18 ~v19
  = du_go'45'fl_5874
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v16 v18
du_go'45'fl_5874 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  Integer -> Maybe Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'fl_5874 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = case coe v13 of
      0 -> case coe v14 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
               -> coe
                    du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180
                          (coe v10)))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'branch'45'scratch'45'zero_2204
                       (coe v7) (coe v9) (coe (0 :: Integer)) (coe v15) (coe v11))
                    (coe v12)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (3 :: Integer))
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> case coe v14 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
               -> coe
                    du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180
                          (coe v10)))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'branch'45'scratch'45'zero_2204
                       (coe v7) (coe v9) (coe v13) (coe v15) (coe v11))
                    (coe v12)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180
                          (coe v10)))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'branch'45'nz_2962
                       (coe v9) (coe v11))
                    (coe v12)
             _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_5886 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_5886 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_5908 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_5908 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_5924 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_5924 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.dc
d_dc_5938 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_5938 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 ~v15 ~v16 ~v17
  = du_dc_5938 v12
du_dc_5938 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_5938 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.d_dataCorr_524
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.halt-s
d_halt'45's_5940 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_5940 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.rbx0
d_rbx0_5942 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rbx0_5942 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.fetch-cmp
d_fetch'45'cmp_5944 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'cmp_5944 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.post-cmp
d_post'45'cmp_5946 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post'45'cmp_5946 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11
                   ~v12 ~v13 ~v14 ~v15 ~v16 ~v17
  = du_post'45'cmp_5946 v10
du_post'45'cmp_5946 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post'45'cmp_5946 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkflags_212
         (coe
            eqInt
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v0))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12))
            (coe (0 :: Integer)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d__'60''7495'__304
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v0))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12))
            (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.step-cmp
d_step'45'cmp_5948 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'cmp_5948 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.fetch-je
d_fetch'45'je_5950 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'je_5950 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.post-je
d_post'45'je_5954 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post'45'je_5954 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16 ~v17
  = du_post'45'je_5954 v10
du_post'45'je_5954 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post'45'je_5954 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkflags_212
         (coe
            eqInt
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v0))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12))
            (coe (0 :: Integer)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d__'60''7495'__304
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v0))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12))
            (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.step-je
d_step'45'je_5956 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'je_5956 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_5966 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_5966 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.result
d_result_5976 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result_5976 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-sv
d_go'45'sv_5982 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'sv_5982 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 ~v14
                ~v15 v16 ~v17
  = du_go'45'sv_5982 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v16
du_go'45'sv_5982 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'sv_5982 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v13 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v14
        -> coe
             du_go'45'fl_5874 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v12) (coe v14)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v1)
                (coe v7) (coe v10))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v14 v15 v16
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.wits
d_wits_6030 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wits_6030 v0 v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10 ~v11 ~v12 v13
            ~v14 ~v15
  = du_wits_6030 v0 v1 v3 v8 v9 v13
du_wits_6030 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wits_6030 v0 v1 v2 v3 v4 v5
  = coe
      du_branch'45'tag'45'scrutinee'45'wf_4098 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe d_inv'45'run_1026 (coe v5))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-fl
d_go'45'fl_6040 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'fl_6040 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 ~v14
                ~v15 ~v16 v17 ~v18 ~v19 ~v20 v21 ~v22
  = du_go'45'fl_6040
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v17 v21
du_go'45'fl_6040 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  Integer -> Maybe Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'fl_6040 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = case coe v13 of
      0 -> case coe v14 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
               -> coe
                    du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182
                          (coe v10)))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'branch'45'tag'45'zero_2354
                       (coe v7) (coe v9) (coe (0 :: Integer)) (coe v15) (coe v11))
                    (coe v12)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (3 :: Integer))
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v15 = subInt (coe v13) (coe (1 :: Integer)) in
           coe
             (case coe v14 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                  -> coe
                       du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182
                             (coe v10)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'branch'45'tag'45'zero_2354
                          (coe v7) (coe v9) (coe v13) (coe v16) (coe v11))
                       (coe v12)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182
                             (coe v10)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'branch'45'tag'45'nz_2746
                          (coe v9) (coe v15) (coe v11))
                       (coe v12)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6058 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6058 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6090 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6090 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6116 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6116 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.dc
d_dc_6140 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_6140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_dc_6140 v12
du_dc_6140 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_6140 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.d_dataCorr_524
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.halt-s
d_halt'45's_6142 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_6142 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.fetch-cmp
d_fetch'45'cmp_6144 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'cmp_6144 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.post-cmp
d_post'45'cmp_6146 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post'45'cmp_6146 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11
                   ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_post'45'cmp_6146 v10
du_post'45'cmp_6146 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post'45'cmp_6146 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkflags_212
         (coe eqInt (coe (0 :: Integer)) (coe (0 :: Integer)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d__'60''7495'__304
            (coe (0 :: Integer)) (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.step-cmp
d_step'45'cmp_6148 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'cmp_6148 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.fetch-je
d_fetch'45'je_6150 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'je_6150 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.post-je
d_post'45'je_6154 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post'45'je_6154 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_post'45'je_6154 v10
du_post'45'je_6154 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post'45'je_6154 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkflags_212
         (coe eqInt (coe (0 :: Integer)) (coe (0 :: Integer)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d__'60''7495'__304
            (coe (0 :: Integer)) (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.step-je
d_step'45'je_6156 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'je_6156 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6162 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6162 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.result
d_result_6176 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result_6176 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-loc
d_go'45'loc_6184 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'loc_6184 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                 ~v14 ~v15 v16 v17 ~v18 ~v19
  = du_go'45'loc_6184
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v16 v17
du_go'45'loc_6184 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'loc_6184 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = coe
      seq (coe v13)
      (coe
         du_go'45'fl_6040 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
         (coe v12) (coe v14)
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v1)
            (coe v7) (coe v10)))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.dc
d_dc_6198 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_6198 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_dc_6198 v12
du_dc_6198 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_6198 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.d_dataCorr_524
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.addr-val
d_addr'45'val_6200 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_addr'45'val_6200 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.rd-heap
d_rd'45'heap_6202 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rd'45'heap_6202 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.dc
d_dc_6218 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_6218 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_dc_6218 v12
du_dc_6218 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_6218 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.d_dataCorr_524
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.spc
d_spc_6220 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_spc_6220 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_spc_6220
du_spc_6220 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_spc_6220 = coe du_stack'45'ptr'45'current_3190
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.st-cf
d_st'45'cf_6222 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_st'45'cf_6222 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.rdi-val
d_rdi'45'val_6226 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45'val_6226 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.rd-stack
d_rd'45'stack_6234 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rd'45'stack_6234 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-sv
d_go'45'sv_6266 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'sv_6266 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13
                ~v14 v15 ~v16
  = du_go'45'sv_6266 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v15
du_go'45'sv_6266 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'sv_6266 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v13
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v13
        -> coe
             du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_454))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'scratch'45'dec_2148
                (coe v9) (coe v10))
             (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v13 v14 v15
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v13
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-sv
d_go'45'sv_6316 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'sv_6316 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13
                ~v14 v15 ~v16
  = du_go'45'sv_6316 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v15
du_go'45'sv_6316 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'sv_6316 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v13
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v13
        -> coe
             du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_460))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'count'45'inc_2096
                (coe v9) (coe v10))
             (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v13 v14 v15
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v13
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.wits
d_wits_6362 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wits_6362 v0 v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10 ~v11 v12 ~v13
            ~v14
  = du_wits_6362 v0 v1 v3 v8 v9 v12
du_wits_6362 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wits_6362 v0 v1 v2 v3 v4 v5
  = coe
      du_load'45'indirect'45'target'45'wf_4190 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe d_inv'45'run_1026 (coe v5))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-mem
d_go'45'mem_6370 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_6370 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13
                 ~v14 ~v15 ~v16 ~v17 v18 ~v19
  = du_go'45'mem_6370 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v18
du_go'45'mem_6370 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_6370 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
        -> coe
             du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'indirect_1200
                (coe v1) (coe v3) (coe v9) (coe v13) (coe v10))
             (coe v11)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6386 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6386 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.stuckp
d_stuckp_6408 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stuckp_6408 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
              ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_stuckp_6408
du_stuckp_6408 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stuckp_6408
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_load'45'indirect'45'heap'45'empty'45'stuck_2502
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.halt-s
d_halt'45's_6410 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_6410 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6412 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6412 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.result
d_result_6422 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result_6422 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-stack
d_go'45'stack_6432 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'stack_6432 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13
                   ~v14 ~v15 ~v16 ~v17 v18 v19 ~v20
  = du_go'45'stack_6432
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v18 v19
du_go'45'stack_6432 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'stack_6432 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      seq (coe v12)
      (case coe v13 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
           -> coe
                du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198)
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'indirect'45'stack_3040
                   (coe v1) (coe v3) (coe v9) (coe v14) (coe v10))
                (coe v11)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                erased
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6452 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6452 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.stuckp
d_stuckp_6482 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stuckp_6482 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
              ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_stuckp_6482
du_stuckp_6482 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stuckp_6482
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_load'45'indirect'45'stack'45'empty'45'stuck_2556
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.halt-s
d_halt'45's_6484 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_6484 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6486 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6486 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.result
d_result_6500 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result_6500 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-loc
d_go'45'loc_6508 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'loc_6508 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13
                 ~v14 v15 ~v16 ~v17
  = du_go'45'loc_6508 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v15
du_go'45'loc_6508 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'loc_6508 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v13 v14
        -> coe
             du_go'45'stack_6432 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe du_stack'45'ptr'45'current_3190)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
                (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v8))
                (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v8)))
                v14)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v13
        -> coe
             du_go'45'mem_6370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
                (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v8)) v13)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.wits
d_wits_6550 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wits_6550 v0 v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10 ~v11 v12 ~v13
            ~v14
  = du_wits_6550 v0 v1 v3 v8 v9 v12
du_wits_6550 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wits_6550 v0 v1 v2 v3 v4 v5
  = coe
      du_load'45'indirect'45'suc'45'target'45'wf_4228 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe d_inv'45'run_1026 (coe v5))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-mem
d_go'45'mem_6558 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_6558 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13
                 ~v14 ~v15 ~v16 ~v17 v18 ~v19
  = du_go'45'mem_6558 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v18
du_go'45'mem_6558 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_6558 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
        -> coe
             du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'indirect'45'suc_1264
                (coe v1) (coe v3) (coe v9) (coe v13) (coe v10))
             (coe v11)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6574 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6574 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.stuckp
d_stuckp_6596 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stuckp_6596 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
              ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_stuckp_6596
du_stuckp_6596 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stuckp_6596
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_load'45'indirect'45'suc'45'heap'45'empty'45'stuck_2618
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.halt-s
d_halt'45's_6598 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_6598 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6600 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6600 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.result
d_result_6610 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result_6610 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-stack
d_go'45'stack_6620 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'stack_6620 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13
                   ~v14 ~v15 ~v16 ~v17 v18 v19 ~v20
  = du_go'45'stack_6620
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v18 v19
du_go'45'stack_6620 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'stack_6620 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      seq (coe v12)
      (case coe v13 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
           -> coe
                du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'indirect'45'suc'45'stack_3120
                   (coe v1) (coe v3) (coe v9) (coe v14) (coe v10))
                (coe v11)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                erased
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6640 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6640 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.stuckp
d_stuckp_6670 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stuckp_6670 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
              ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_stuckp_6670
du_stuckp_6670 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stuckp_6670
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_load'45'indirect'45'suc'45'stack'45'empty'45'stuck_2676
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.halt-s
d_halt'45's_6672 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_6672 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6674 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6674 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.result
d_result_6688 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result_6688 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-loc
d_go'45'loc_6696 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'loc_6696 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13
                 ~v14 v15 ~v16 ~v17
  = du_go'45'loc_6696 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v15
du_go'45'loc_6696 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'loc_6696 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v13 v14
        -> coe
             du_go'45'stack_6620 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe du_stack'45'ptr'45'current'45'suc_3212)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
                (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v8))
                (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v8)))
                (addInt (coe (1 :: Integer)) (coe v14)))
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v13
        -> coe
             du_go'45'mem_6558 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
                (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v8))
                (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v13)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-mem
d_go'45'mem_6744 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_6744 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                 ~v14 ~v15 v16 ~v17
  = du_go'45'mem_6744 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v16
du_go'45'mem_6744 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_6744 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v13 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
        -> coe
             du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                (coe v10))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'from'45'slot_1332
                (coe v1) (coe v3) (coe v9) (coe v14) (coe v11))
             (coe v12)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_slot'45'empty'45'stop_1632
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6754 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6754 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6766 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6766 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-mem
d_go'45'mem_6804 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_6804 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                 ~v14 ~v15 v16 ~v17
  = du_go'45'mem_6804 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v16
du_go'45'mem_6804 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_6804 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v13 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
        -> coe
             du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2212
                (coe v10))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'restore'45'input_1392
                (coe v1) (coe v3) (coe v9) (coe v14) (coe v11))
             (coe v12)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_slot'45'empty'45'stop_1632
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6814 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6814 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6826 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6826 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-mem
d_go'45'mem_6864 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_6864 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                 ~v14 ~v15 v16 ~v17
  = du_go'45'mem_6864 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v16
du_go'45'mem_6864 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_6864 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v13 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
        -> coe
             du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2230
                (coe v10))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'worklist'45'pop_1844
                (coe v1) (coe v3) (coe v9) (coe v14) (coe v11))
             (coe v12)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_slot'45'empty'45'stop_1632
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6874 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6874 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6886 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6886 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-ptr
d_go'45'ptr_6922 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'ptr_6922 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13
                 ~v14 v15 ~v16
  = du_go'45'ptr_6922 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v15
du_go'45'ptr_6922 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'ptr_6922 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v13
        -> case coe v13 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v14 v15
               -> coe
                    du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                    (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'store'45'indirect'45'stack_3204
                       (coe v1) (coe v3) (coe v8) (coe v9) (coe v15) (coe v10))
                    (coe v11)
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v14
               -> coe
                    du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                    (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'store'45'indirect_1902
                       (coe v8) (coe v9) (coe v14) (coe v10)
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'sized_446
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.d_dataCorr_524
                             (coe v10))
                          v14
                          (coe
                             du_store'45'indirect'45'inbounds_4148 (coe v0) (coe v1) (coe v7)
                             (coe v8) (coe v14) (coe d_inv'45'run_1026 (coe v11)))))
                    (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v13
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v13 v14 v15
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v13
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6932 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6932 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6948 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6948 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-ptr
d_go'45'ptr_6996 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'ptr_6996 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13
                 ~v14 v15 ~v16
  = du_go'45'ptr_6996 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v15
du_go'45'ptr_6996 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'ptr_6996 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v13
        -> case coe v13 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v14 v15
               -> coe
                    du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'store'45'indirect'45'suc'45'stack_3288
                       (coe v1) (coe v3) (coe v8) (coe v9) (coe v15) (coe v10))
                    (coe v11)
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v14
               -> coe
                    du_ccc'45'step'45'bs_4332 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'store'45'indirect'45'suc_1966
                       (coe v8) (coe v9) (coe v14) (coe v10)
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'sized_446
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.d_dataCorr_524
                             (coe v10))
                          (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v14))
                          (coe
                             du_store'45'indirect'45'suc'45'inbounds_4168 (coe v0) (coe v1)
                             (coe v7) (coe v8) (coe d_inv'45'run_1026 (coe v11)))))
                    (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v13
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v13 v14 v15
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v13
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_7006 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_7006 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_7022 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_7022 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-eff
d_go'45'eff_7076 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'eff_7076 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15 ~v16 ~v17 v18 ~v19
  = du_go'45'eff_7076
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v18
du_go'45'eff_7076 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'eff_7076 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15
  = case coe v15 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_124
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_rec_7088 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                      (coe v13) (coe v14))))
             erased
      MAlonzo.Code.Once.SigOp.Info.C_Emits_126
        -> coe
             du_sigop'45'external_4608 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14)
      MAlonzo.Code.Once.SigOp.Info.C_Halts_128
        -> coe
             du_sigop'45'external_4608 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.contract
d_contract_7084 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_contract_7084 v0 v1 ~v2 v3 v4 ~v5 ~v6 v7 v8 v9 v10 v11 v12 v13
                v14 v15 ~v16 ~v17 ~v18
  = du_contract_7084 v0 v1 v3 v4 v7 v8 v9 v10 v11 v12 v13 v14 v15
du_contract_7084 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_contract_7084 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      d_arith'45'sigop'45'contract_1882 v0 v1 erased v2 v3 v4 v5 v6 v7 v8
      v9 v10 (d_inv'45'run_1026 (coe v12)) erased erased v11 erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.pl
d_pl_7086 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pl_7086 v0 v1 ~v2 v3 v4 ~v5 ~v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
          ~v16 ~v17 ~v18
  = du_pl_7086 v0 v1 v3 v4 v7 v8 v9 v10 v11 v12 v13 v14 v15
du_pl_7086 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pl_7086 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         du_contract_7084 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
         (coe v12))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.rec
d_rec_7088 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rec_7088 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
           ~v16 ~v17 ~v18
  = du_rec_7088 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
du_rec_7088 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rec_7088 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = coe
      du_events'45'agree_4274 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6) (coe v7)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_242
         (coe v1)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2238
            (coe v10) (coe v11) (coe v12))
         (coe v8))
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v15 v16 v17 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
              (\ v18 v19 v20 ->
                 coe
                   MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z64.du_val'45'x86'45'64_160
                   v18 v19)
              v15 v17)
         (coe
            du_pl_7086 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
            (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13)
            (coe v14))
         v9)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               du_contract_7084 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6)
               (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13)
               (coe v14))))
      (coe
         du_flat'45'inv'45'step_1060 (coe v1)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2238
            (coe v10) (coe v11) (coe v12))
         (coe v7) (coe v8) (coe v14))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.goal
d_goal_7090 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_goal_7090 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.contract
d_contract_7126 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_contract_7126 v0 v1 ~v2 v3 v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                v15 ~v16 ~v17
  = du_contract_7126 v0 v1 v3 v4 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
du_contract_7126 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_contract_7126 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      d_external'45'sigop'45'contract_1902 v0 v1 erased v2 v3 v4 v5 v6 v7
      v8 v9 v10 v11 (d_inv'45'run_1026 (coe v13)) erased erased v12
      erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.rec
d_rec_7128 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rec_7128 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
           ~v16 ~v17
  = du_rec_7128 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
du_rec_7128 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rec_7128 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = coe
      du_events'45'agree_4274 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6) (coe v7)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_242
         (coe v1)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2238
            (coe v10) (coe v11) (coe v12))
         (coe v8))
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.RunTrace.d_ret'45'past_14
         (coe v9))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               du_contract_7126 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
               (coe v13) (coe v14))))
      (coe
         du_flat'45'inv'45'step_1060 (coe v1)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2238
            (coe v10) (coe v11) (coe v12))
         (coe v7) (coe v8) (coe v14))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.goal
d_goal_7130 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_goal_7130 = erased
