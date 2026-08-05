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
import qualified MAlonzo.Code.Once.CCC.Codegen.ShapeTable
import qualified MAlonzo.Code.Once.CCC.Codegen.SlotBudget
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
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
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.readLoc
d_readLoc_28 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_readLoc_28 ~v0 ~v1 ~v2 = du_readLoc_28
du_readLoc_28 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_readLoc_28
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.writeLoc
d_writeLoc_30 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_writeLoc_30 v0 ~v1 ~v2 = du_writeLoc_30 v0
du_writeLoc_30 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_writeLoc_30 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_792 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.writeLocToHeap
d_writeLocToHeap_34 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_writeLocToHeap_34 ~v0 ~v1 ~v2 = du_writeLocToHeap_34
du_writeLocToHeap_34 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_writeLocToHeap_34
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_784
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.Frame
d_Frame_38 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  ()
d_Frame_38 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.FlatState
d_FlatState_42 a0 a1 a2 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.do-branch
d_do'45'branch_50 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_do'45'branch_50 v0 ~v1 ~v2 = du_do'45'branch_50 v0
du_do'45'branch_50 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_do'45'branch_50 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'branch_232 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.do-jump
d_do'45'jump_52 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_do'45'jump_52 ~v0 ~v1 ~v2 = du_do'45'jump_52
du_do'45'jump_52 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_do'45'jump_52
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_224
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.fetch
d_fetch_90 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
d_fetch_90 ~v0 ~v1 ~v2 = du_fetch_90
du_fetch_90 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
du_fetch_90 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_216
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.find-label
d_find'45'label_98 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> Maybe Integer
d_find'45'label_98 v0 ~v1 ~v2 = du_find'45'label_98 v0
du_find'45'label_98 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> Maybe Integer
du_find'45'label_98 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.flat-exec-instr
d_flat'45'exec'45'instr_110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_flat'45'exec'45'instr_110 v0 ~v1 ~v2
  = du_flat'45'exec'45'instr_110 v0
du_flat'45'exec'45'instr_110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_flat'45'exec'45'instr_110 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_570
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.FlatState.falloc
d_falloc_174 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_falloc_174 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.FlatState.fclosure
d_fclosure_176 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fclosure_176 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_82 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.FlatState.floc
d_floc_178 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_floc_178 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.FlatState.fpc
d_fpc_180 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> Integer
d_fpc_180 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.FlatState.fret
d_fret_182 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> [Integer]
d_fret_182 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.BlockStep
d_BlockStep_186 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 -> ()
d_BlockStep_186 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.BlockStepAt
d_BlockStepAt_188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 -> ()
d_BlockStepAt_188 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.CompiledCorr
d_CompiledCorr_190 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.b-cmp-reg-imm
d_b'45'cmp'45'reg'45'imm_194 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_b'45'cmp'45'reg'45'imm_194 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.b-mov-reg-imm
d_b'45'mov'45'reg'45'imm_196 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_b'45'mov'45'reg'45'imm_196 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.b-mov-reg-reg
d_b'45'mov'45'reg'45'reg_198 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_b'45'mov'45'reg'45'reg_198 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-alloc-heap
d_block'45'step'45'alloc'45'heap_200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'alloc'45'heap_200 ~v0 ~v1 ~v2
  = du_block'45'step'45'alloc'45'heap_200
du_block'45'step'45'alloc'45'heap_200 ::
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
du_block'45'step'45'alloc'45'heap_200 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                      v10 v11 v12 v13 v14 v15
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'alloc'45'heap_2834
      v2 v3 v4 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-alloc-stack
d_block'45'step'45'alloc'45'stack_202 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'alloc'45'stack_202 v0 ~v1 ~v2
  = du_block'45'step'45'alloc'45'stack_202 v0
du_block'45'step'45'alloc'45'stack_202 ::
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
du_block'45'step'45'alloc'45'stack_202 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                       v9 v10 v11 v12 v13 v14 v15
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'alloc'45'stack_1460
      (coe v0) v3 v4 v5 v6 v14
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-c-branch-nz
d_block'45'step'45'c'45'branch'45'nz_204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'c'45'branch'45'nz_204 ~v0 ~v1 ~v2
  = du_block'45'step'45'c'45'branch'45'nz_204
du_block'45'step'45'c'45'branch'45'nz_204 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'c'45'branch'45'nz_204 v0 v1 v2 v3 v4 v5 v6 v7
                                          v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'branch'45'nz_2962
      v3 v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-c-branch-scratch-zero
d_block'45'step'45'c'45'branch'45'scratch'45'zero_206 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'c'45'branch'45'scratch'45'zero_206 ~v0 ~v1 ~v2
  = du_block'45'step'45'c'45'branch'45'scratch'45'zero_206
du_block'45'step'45'c'45'branch'45'scratch'45'zero_206 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'c'45'branch'45'scratch'45'zero_206 v0 v1 v2 v3
                                                       v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'branch'45'scratch'45'zero_2204
      v1 v3 v5 v6 v7
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-c-branch-tag-nz
d_block'45'step'45'c'45'branch'45'tag'45'nz_208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'c'45'branch'45'tag'45'nz_208 ~v0 ~v1 ~v2
  = du_block'45'step'45'c'45'branch'45'tag'45'nz_208
du_block'45'step'45'c'45'branch'45'tag'45'nz_208 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'c'45'branch'45'tag'45'nz_208 v0 v1 v2 v3 v4 v5
                                                 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'branch'45'tag'45'nz_2746
      v3 v6 v7
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-c-branch-tag-zero
d_block'45'step'45'c'45'branch'45'tag'45'zero_210 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
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
d_block'45'step'45'c'45'branch'45'tag'45'zero_210 ~v0 ~v1 ~v2
  = du_block'45'step'45'c'45'branch'45'tag'45'zero_210
du_block'45'step'45'c'45'branch'45'tag'45'zero_210 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
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
du_block'45'step'45'c'45'branch'45'tag'45'zero_210 v0 v1 v2 v3 v4
                                                   v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'branch'45'tag'45'zero_2354
      v1 v3 v6 v7 v8
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-c-jmp
d_block'45'step'45'c'45'jmp_212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'c'45'jmp_212 ~v0 ~v1 ~v2
  = du_block'45'step'45'c'45'jmp_212
du_block'45'step'45'c'45'jmp_212 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'c'45'jmp_212 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'jmp_1140
      v1 v3 v5 v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-c-label
d_block'45'step'45'c'45'label_214 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'c'45'label_214 ~v0 ~v1 ~v2
  = du_block'45'step'45'c'45'label_214
du_block'45'step'45'c'45'label_214 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'c'45'label_214 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'label_986
      v3 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-count-inc
d_block'45'step'45'count'45'inc_216 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'count'45'inc_216 ~v0 ~v1 ~v2
  = du_block'45'step'45'count'45'inc_216
du_block'45'step'45'count'45'inc_216 ::
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
du_block'45'step'45'count'45'inc_216 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'count'45'inc_2096
      v3 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-count-zero
d_block'45'step'45'count'45'zero_218 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'count'45'zero_218 ~v0 ~v1 ~v2
  = du_block'45'step'45'count'45'zero_218
du_block'45'step'45'count'45'zero_218 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'count'45'zero_218 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'count'45'zero_936
      v3 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-dealloc-stack
d_block'45'step'45'dealloc'45'stack_220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'dealloc'45'stack_220 v0 ~v1 ~v2
  = du_block'45'step'45'dealloc'45'stack_220 v0
du_block'45'step'45'dealloc'45'stack_220 ::
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
du_block'45'step'45'dealloc'45'stack_220 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'dealloc'45'stack_1528
      (coe v0) v3 v4 v5 v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-lea-slot
d_block'45'step'45'lea'45'slot_222 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'lea'45'slot_222 ~v0 ~v1 ~v2
  = du_block'45'step'45'lea'45'slot_222
du_block'45'step'45'lea'45'slot_222 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'lea'45'slot_222 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'lea'45'slot_2910
      v3 v4 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-load-code-addr
d_block'45'step'45'load'45'code'45'addr_224 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'load'45'code'45'addr_224 ~v0 ~v1 ~v2
  = du_block'45'step'45'load'45'code'45'addr_224
du_block'45'step'45'load'45'code'45'addr_224 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'load'45'code'45'addr_224 v0 v1 v2 v3 v4 v5 v6
                                             v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'code'45'addr_1684
      v3 v4 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-load-const
d_block'45'step'45'load'45'const_226 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'load'45'const_226 ~v0 ~v1 ~v2
  = du_block'45'step'45'load'45'const_226
du_block'45'step'45'load'45'const_226 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'load'45'const_226 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'const_1584
      v3 v4 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-load-const-float
d_block'45'step'45'load'45'const'45'float_228 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'load'45'const'45'float_228 ~v0 ~v1 ~v2
  = du_block'45'step'45'load'45'const'45'float_228
du_block'45'step'45'load'45'const'45'float_228 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'load'45'const'45'float_228 v0 v1 v2 v3 v4 v5 v6
                                               v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'const'45'float_1634
      v3 v4 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-load-from-slot
d_block'45'step'45'load'45'from'45'slot_230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'load'45'from'45'slot_230 v0 ~v1 ~v2
  = du_block'45'step'45'load'45'from'45'slot_230 v0
du_block'45'step'45'load'45'from'45'slot_230 ::
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
du_block'45'step'45'load'45'from'45'slot_230 v0 v1 v2 v3 v4 v5 v6
                                             v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'from'45'slot_1332
      (coe v0) v1 v4 v6 v7
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-load-indirect
d_block'45'step'45'load'45'indirect_232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'load'45'indirect_232 v0 ~v1 ~v2
  = du_block'45'step'45'load'45'indirect_232 v0
du_block'45'step'45'load'45'indirect_232 ::
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
du_block'45'step'45'load'45'indirect_232 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'indirect_1200
      (coe v0) v1 v4 v6 v7
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-load-indirect-stack
d_block'45'step'45'load'45'indirect'45'stack_234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'load'45'indirect'45'stack_234 v0 ~v1 ~v2
  = du_block'45'step'45'load'45'indirect'45'stack_234 v0
du_block'45'step'45'load'45'indirect'45'stack_234 ::
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
du_block'45'step'45'load'45'indirect'45'stack_234 v0 v1 v2 v3 v4 v5
                                                  v6 v7 v8 v9 v10 v11 v12 v13 v14
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'indirect'45'stack_3040
      (coe v0) v1 v4 v7 v8
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-load-indirect-suc
d_block'45'step'45'load'45'indirect'45'suc_236 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'load'45'indirect'45'suc_236 v0 ~v1 ~v2
  = du_block'45'step'45'load'45'indirect'45'suc_236 v0
du_block'45'step'45'load'45'indirect'45'suc_236 ::
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
du_block'45'step'45'load'45'indirect'45'suc_236 v0 v1 v2 v3 v4 v5
                                                v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'indirect'45'suc_1264
      (coe v0) v1 v4 v6 v7
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-load-indirect-suc-stack
d_block'45'step'45'load'45'indirect'45'suc'45'stack_238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'load'45'indirect'45'suc'45'stack_238 v0 ~v1 ~v2
  = du_block'45'step'45'load'45'indirect'45'suc'45'stack_238 v0
du_block'45'step'45'load'45'indirect'45'suc'45'stack_238 ::
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
du_block'45'step'45'load'45'indirect'45'suc'45'stack_238 v0 v1 v2
                                                         v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'indirect'45'suc'45'stack_3120
      (coe v0) v1 v4 v7 v8
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-load-tag-lit
d_block'45'step'45'load'45'tag'45'lit_240 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'load'45'tag'45'lit_240 ~v0 ~v1 ~v2
  = du_block'45'step'45'load'45'tag'45'lit_240
du_block'45'step'45'load'45'tag'45'lit_240 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'load'45'tag'45'lit_240 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'tag'45'lit_862
      v3 v4 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-mov-input2-to-output
d_block'45'step'45'mov'45'input2'45'to'45'output_242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'mov'45'input2'45'to'45'output_242 ~v0 ~v1 ~v2
  = du_block'45'step'45'mov'45'input2'45'to'45'output_242
du_block'45'step'45'mov'45'input2'45'to'45'output_242 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'mov'45'input2'45'to'45'output_242 v0 v1 v2 v3
                                                      v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'mov'45'input2'45'to'45'output_736
      v3 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-mov-output-to-input2
d_block'45'step'45'mov'45'output'45'to'45'input2_244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'mov'45'output'45'to'45'input2_244 ~v0 ~v1 ~v2
  = du_block'45'step'45'mov'45'output'45'to'45'input2_244
du_block'45'step'45'mov'45'output'45'to'45'input2_244 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'mov'45'output'45'to'45'input2_244 v0 v1 v2 v3
                                                      v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'mov'45'output'45'to'45'input2_760
      v3 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-mov-ri
d_block'45'step'45'mov'45'ri_246 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'mov'45'ri_246 ~v0 ~v1 ~v2
  = du_block'45'step'45'mov'45'ri_246
du_block'45'step'45'mov'45'ri_246 ::
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
du_block'45'step'45'mov'45'ri_246 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                  v11 v12
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'mov'45'ri_790
      v3 v5 v6 v12
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-mov-rr
d_block'45'step'45'mov'45'rr_248 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'mov'45'rr_248 ~v0 ~v1 ~v2
  = du_block'45'step'45'mov'45'rr_248
du_block'45'step'45'mov'45'rr_248 ::
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
du_block'45'step'45'mov'45'rr_248 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                  v11 v12
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'mov'45'rr_618
      v3 v5 v6 v12
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-mov-to-input
d_block'45'step'45'mov'45'to'45'input_250 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'mov'45'to'45'input_250 ~v0 ~v1 ~v2
  = du_block'45'step'45'mov'45'to'45'input_250
du_block'45'step'45'mov'45'to'45'input_250 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'mov'45'to'45'input_250 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'mov'45'to'45'input_712
      v3 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-mov-to-output
d_block'45'step'45'mov'45'to'45'output_252 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'mov'45'to'45'output_252 ~v0 ~v1 ~v2
  = du_block'45'step'45'mov'45'to'45'output_252
du_block'45'step'45'mov'45'to'45'output_252 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'mov'45'to'45'output_252 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'mov'45'to'45'output_688
      v3 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-reclaim-to
d_block'45'step'45'reclaim'45'to_254 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'reclaim'45'to_254 ~v0 ~v1 ~v2
  = du_block'45'step'45'reclaim'45'to_254
du_block'45'step'45'reclaim'45'to_254 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'reclaim'45'to_254 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'reclaim'45'to_1104
      v3 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-restore-input
d_block'45'step'45'restore'45'input_256 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'restore'45'input_256 v0 ~v1 ~v2
  = du_block'45'step'45'restore'45'input_256 v0
du_block'45'step'45'restore'45'input_256 ::
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
du_block'45'step'45'restore'45'input_256 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9 v10 v11
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'restore'45'input_1392
      (coe v0) v1 v4 v6 v7
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-save-closure-reg
d_block'45'step'45'save'45'closure'45'reg_258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'save'45'closure'45'reg_258 ~v0 ~v1 ~v2
  = du_block'45'step'45'save'45'closure'45'reg_258
du_block'45'step'45'save'45'closure'45'reg_258 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'save'45'closure'45'reg_258 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'save'45'closure'45'reg_1732
      v3 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-scratch-dec
d_block'45'step'45'scratch'45'dec_260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'scratch'45'dec_260 ~v0 ~v1 ~v2
  = du_block'45'step'45'scratch'45'dec_260
du_block'45'step'45'scratch'45'dec_260 ::
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
du_block'45'step'45'scratch'45'dec_260 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'scratch'45'dec_2148
      v3 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-scratch-load-count
d_block'45'step'45'scratch'45'load'45'count_262 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'scratch'45'load'45'count_262 ~v0 ~v1 ~v2
  = du_block'45'step'45'scratch'45'load'45'count_262
du_block'45'step'45'scratch'45'load'45'count_262 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'scratch'45'load'45'count_262 v0 v1 v2 v3 v4 v5
                                                 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'scratch'45'load'45'count_960
      v3 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-scratch-one
d_block'45'step'45'scratch'45'one_264 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'scratch'45'one_264 ~v0 ~v1 ~v2
  = du_block'45'step'45'scratch'45'one_264
du_block'45'step'45'scratch'45'one_264 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'scratch'45'one_264 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'scratch'45'one_888
      v3 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-scratch-zero
d_block'45'step'45'scratch'45'zero_266 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'scratch'45'zero_266 ~v0 ~v1 ~v2
  = du_block'45'step'45'scratch'45'zero_266
du_block'45'step'45'scratch'45'zero_266 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'scratch'45'zero_266 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'scratch'45'zero_912
      v3 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-store-at-slot
d_block'45'step'45'store'45'at'45'slot_268 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'store'45'at'45'slot_268 ~v0 ~v1 ~v2
  = du_block'45'step'45'store'45'at'45'slot_268
du_block'45'step'45'store'45'at'45'slot_268 ::
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
du_block'45'step'45'store'45'at'45'slot_268 v0 v1 v2 v3 v4 v5 v6 v7
                                            v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'store'45'at'45'slot_2036
      v2 v3 v4 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-store-indirect
d_block'45'step'45'store'45'indirect_270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'store'45'indirect_270 ~v0 ~v1 ~v2
  = du_block'45'step'45'store'45'indirect_270
du_block'45'step'45'store'45'indirect_270 ::
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
du_block'45'step'45'store'45'indirect_270 v0 v1 v2 v3 v4 v5 v6 v7
                                          v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'store'45'indirect_1902
      v2 v3 v4 v5 v9
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-store-indirect-stack
d_block'45'step'45'store'45'indirect'45'stack_272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'store'45'indirect'45'stack_272 v0 ~v1 ~v2
  = du_block'45'step'45'store'45'indirect'45'stack_272 v0
du_block'45'step'45'store'45'indirect'45'stack_272 ::
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
du_block'45'step'45'store'45'indirect'45'stack_272 v0 v1 v2 v3 v4
                                                   v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'store'45'indirect'45'stack_3204
      (coe v0) v1 v3 v4 v6 v7
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-store-indirect-suc
d_block'45'step'45'store'45'indirect'45'suc_274 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'store'45'indirect'45'suc_274 ~v0 ~v1 ~v2
  = du_block'45'step'45'store'45'indirect'45'suc_274
du_block'45'step'45'store'45'indirect'45'suc_274 ::
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
du_block'45'step'45'store'45'indirect'45'suc_274 v0 v1 v2 v3 v4 v5
                                                 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'store'45'indirect'45'suc_1966
      v2 v3 v4 v5 v9
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-store-indirect-suc-stack
d_block'45'step'45'store'45'indirect'45'suc'45'stack_276 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'store'45'indirect'45'suc'45'stack_276 v0 ~v1 ~v2
  = du_block'45'step'45'store'45'indirect'45'suc'45'stack_276 v0
du_block'45'step'45'store'45'indirect'45'suc'45'stack_276 ::
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
du_block'45'step'45'store'45'indirect'45'suc'45'stack_276 v0 v1 v2
                                                          v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'store'45'indirect'45'suc'45'stack_3288
      (coe v0) v1 v3 v4 v6 v7
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-worklist-check
d_block'45'step'45'worklist'45'check_278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'worklist'45'check_278 ~v0 ~v1 ~v2
  = du_block'45'step'45'worklist'45'check_278
du_block'45'step'45'worklist'45'check_278 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'worklist'45'check_278 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'worklist'45'check_1070
      v3 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-worklist-init
d_block'45'step'45'worklist'45'init_280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'worklist'45'init_280 ~v0 ~v1 ~v2
  = du_block'45'step'45'worklist'45'init_280
du_block'45'step'45'worklist'45'init_280 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'worklist'45'init_280 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'worklist'45'init_1036
      v3 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-worklist-pop
d_block'45'step'45'worklist'45'pop_282 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'worklist'45'pop_282 v0 ~v1 ~v2
  = du_block'45'step'45'worklist'45'pop_282 v0
du_block'45'step'45'worklist'45'pop_282 ::
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
du_block'45'step'45'worklist'45'pop_282 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'worklist'45'pop_1844
      (coe v0) v1 v4 v6 v7
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.block-step-worklist-push
d_block'45'step'45'worklist'45'push_284 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'step'45'worklist'45'push_284 ~v0 ~v1 ~v2
  = du_block'45'step'45'worklist'45'push_284
du_block'45'step'45'worklist'45'push_284 ::
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
du_block'45'step'45'worklist'45'push_284 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'worklist'45'push_1782
      v2 v3 v4 v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.dataCorr
d_dataCorr_286 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dataCorr_286 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.d_dataCorr_524
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.load-indirect-heap-empty-stuck
d_load'45'indirect'45'heap'45'empty'45'stuck_288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_load'45'indirect'45'heap'45'empty'45'stuck_288 ~v0 ~v1 ~v2
  = du_load'45'indirect'45'heap'45'empty'45'stuck_288
du_load'45'indirect'45'heap'45'empty'45'stuck_288 ::
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
du_load'45'indirect'45'heap'45'empty'45'stuck_288 v0 v1 v2 v3 v4 v5
                                                  v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_load'45'indirect'45'heap'45'empty'45'stuck_2502
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.load-indirect-stack-empty-stuck
d_load'45'indirect'45'stack'45'empty'45'stuck_290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_load'45'indirect'45'stack'45'empty'45'stuck_290 ~v0 ~v1 ~v2
  = du_load'45'indirect'45'stack'45'empty'45'stuck_290
du_load'45'indirect'45'stack'45'empty'45'stuck_290 ::
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
du_load'45'indirect'45'stack'45'empty'45'stuck_290 v0 v1 v2 v3 v4
                                                   v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_load'45'indirect'45'stack'45'empty'45'stuck_2556
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.load-indirect-suc-heap-empty-stuck
d_load'45'indirect'45'suc'45'heap'45'empty'45'stuck_292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_load'45'indirect'45'suc'45'heap'45'empty'45'stuck_292 ~v0 ~v1 ~v2
  = du_load'45'indirect'45'suc'45'heap'45'empty'45'stuck_292
du_load'45'indirect'45'suc'45'heap'45'empty'45'stuck_292 ::
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
du_load'45'indirect'45'suc'45'heap'45'empty'45'stuck_292 v0 v1 v2
                                                         v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_load'45'indirect'45'suc'45'heap'45'empty'45'stuck_2618
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.load-indirect-suc-stack-empty-stuck
d_load'45'indirect'45'suc'45'stack'45'empty'45'stuck_294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_load'45'indirect'45'suc'45'stack'45'empty'45'stuck_294 ~v0 ~v1
                                                         ~v2
  = du_load'45'indirect'45'suc'45'stack'45'empty'45'stuck_294
du_load'45'indirect'45'suc'45'stack'45'empty'45'stuck_294 ::
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
du_load'45'indirect'45'suc'45'stack'45'empty'45'stuck_294 v0 v1 v2
                                                          v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_load'45'indirect'45'suc'45'stack'45'empty'45'stuck_2676
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.pc-off
d_pc'45'off_296 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pc'45'off_296 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.+-not-<
d_'43''45'not'45''60'_300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'43''45'not'45''60'_300 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.AddrMap
d_AddrMap_302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  ()
d_AddrMap_302 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.ExtDom
d_ExtDom_304 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr
d_FlatCorr_306 a0 a1 a2 a3 a4 a5 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.HDom
d_HDom_310 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> ()
d_HDom_310 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.HeapView
d_HeapView_312 a0 a1 a2 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.StackWindows
d_StackWindows_316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_StackWindows_316 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.Window
d_Window_318 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_Window_318 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.atstack-frame-inj
d_atstack'45'frame'45'inj_320 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atstack'45'frame'45'inj_320 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.atstack-slot-inj
d_atstack'45'slot'45'inj_322 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atstack'45'slot'45'inj_322 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.dec-enc
d_dec'45'enc_324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dec'45'enc_324 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.descend-view
d_descend'45'view_326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218
d_descend'45'view_326 ~v0 ~v1 ~v2 = du_descend'45'view_326
du_descend'45'view_326 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218
du_descend'45'view_326 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_descend'45'view_586
      v0 v1 v3
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.dom-below
d_dom'45'below_328 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_328 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'below_262
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.dom-fresh
d_dom'45'fresh_330 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'fresh_330 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'fresh_436
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.dom-sized
d_dom'45'sized_332 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_dom'45'sized_332 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'sized_446
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.dom-written
d_dom'45'written_334 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_dom'45'written_334 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'written_442
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.enc-ext
d_enc'45'ext_336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_enc'45'ext_336 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.enc-ext-maybe
d_enc'45'ext'45'maybe_338 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_enc'45'ext'45'maybe_338 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.enc-maybe
d_enc'45'maybe_340 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
d_enc'45'maybe_340 v0 ~v1 ~v2 = du_enc'45'maybe_340 v0
du_enc'45'maybe_340 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
du_enc'45'maybe_340 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_enc'45'maybe_316
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.enc-maybe-at
d_enc'45'maybe'45'at_342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
d_enc'45'maybe'45'at_342 v0 ~v1 ~v2 = du_enc'45'maybe'45'at_342 v0
du_enc'45'maybe'45'at_342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
du_enc'45'maybe'45'at_342 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_enc'45'maybe'45'at_304
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.enc-sv
d_enc'45'sv_344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
d_enc'45'sv_344 v0 ~v1 ~v2 = du_enc'45'sv_344 v0
du_enc'45'sv_344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
du_enc'45'sv_344 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_enc'45'sv_312
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.enc-sv-at
d_enc'45'sv'45'at_346 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
d_enc'45'sv'45'at_346 v0 ~v1 ~v2 = du_enc'45'sv'45'at_346 v0
du_enc'45'sv'45'at_346 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
du_enc'45'sv'45'at_346 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_enc'45'sv'45'at_276
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.enc-zero
d_enc'45'zero_348 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'zero_348 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.ext-addr
d_ext'45'addr_350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_ext'45'addr_350 ~v0 ~v1 ~v2 = du_ext'45'addr_350
du_ext'45'addr_350 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
du_ext'45'addr_350
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_ext'45'addr_2184
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.ext-addr-aux
d_ext'45'addr'45'aux_352 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
d_ext'45'addr'45'aux_352 ~v0 ~v1 ~v2 = du_ext'45'addr'45'aux_352
du_ext'45'addr'45'aux_352 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
du_ext'45'addr'45'aux_352 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_ext'45'addr'45'aux_2166
      v0 v1 v3
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.ext-addr-base
d_ext'45'addr'45'base_354 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'base_354 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.ext-addr-fresh
d_ext'45'addr'45'fresh_356 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'fresh_356 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.ext-addr-old
d_ext'45'addr'45'old_358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'old_358 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.ext-suc
d_ext'45'suc_364 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'suc_364 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.ext-suc-aux
d_ext'45'suc'45'aux_366 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'suc'45'aux_366 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.extend-view
d_extend'45'view_368 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_extend'45'view_368 ~v0 ~v1 ~v2 = du_extend'45'view_368
du_extend'45'view_368 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218
du_extend'45'view_368 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_extend'45'view_2342
      v0 v1 v2 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.frames-of
d_frames'45'of_370 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_frames'45'of_370 ~v0 ~v1 ~v2 = du_frames'45'of_370
du_frames'45'of_370 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_frames'45'of_370
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_frames'45'of_320
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.front-lo
d_front'45'lo_372 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo_372 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_front'45'lo_266
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.haddr
d_haddr_374 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_haddr_374 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_haddr_244
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.haddr-inj
d_haddr'45'inj_376 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_376 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.haddr-suc
d_haddr'45'suc_378 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_378 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.halt-eq
d_halt'45'eq_380 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45'eq_380 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.heap-eq
d_heap'45'eq_382 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'eq_382 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.hfront
d_hfront_384 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer
d_hfront_384 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_hfront_248
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.inc-enc
d_inc'45'enc_386 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inc'45'enc_386 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.lit-word
d_lit'45'word_388 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer -> Integer
d_lit'45'word_388 ~v0 ~v1 ~v2 v3 = du_lit'45'word_388 v3
du_lit'45'word_388 :: Integer -> Integer
du_lit'45'word_388 v0 = coe v0
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.lo
d_lo_390 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer
d_lo_390 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_lo_264
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.lo-le
d_lo'45'le_392 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'le_392 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_lo'45'le_452
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.r14-eq
d_r14'45'eq_396 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r14'45'eq_396 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.r15-eq
d_r15'45'eq_398 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r15'45'eq_398 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.rax-eq
d_rax'45'eq_400 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rax'45'eq_400 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.rbx-eq
d_rbx'45'eq_402 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rbx'45'eq_402 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.rdi-eq
d_rdi'45'eq_404 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45'eq_404 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.read-write-miss
d_read'45'write'45'miss_406 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_read'45'write'45'miss_406 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.rsi-eq
d_rsi'45'eq_408 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rsi'45'eq_408 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.rsp-eq
d_rsp'45'eq_410 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rsp'45'eq_410 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sep
d_sep_412 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sep_412 v0 ~v1 ~v2 v3 = du_sep_412 v0 v3
du_sep_412 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sep_412 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_front'45'lo_266
         (coe v0))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_lo'45'le_452
         (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-alloc-heap
d_sim'45'alloc'45'heap_414 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_sim'45'alloc'45'heap_414 ~v0 ~v1 ~v2
  = du_sim'45'alloc'45'heap_414
du_sim'45'alloc'45'heap_414 ::
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
du_sim'45'alloc'45'heap_414 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12 v13 v14
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'alloc'45'heap_2680
      v4 v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-alloc-stack
d_sim'45'alloc'45'stack_416 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_sim'45'alloc'45'stack_416 v0 ~v1 ~v2
  = du_sim'45'alloc'45'stack_416 v0
du_sim'45'alloc'45'stack_416 ::
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
du_sim'45'alloc'45'stack_416 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12 v13
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'alloc'45'stack_1916
      (coe v0) v2 v4 v6 v12
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-dealloc-stack
d_sim'45'dealloc'45'stack_418 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_sim'45'dealloc'45'stack_418 v0 ~v1 ~v2
  = du_sim'45'dealloc'45'stack_418 v0
du_sim'45'dealloc'45'stack_418 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'dealloc'45'stack_418 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'dealloc'45'stack_1980
      (coe v0) v4 v5 v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-lea-slot
d_sim'45'lea'45'slot_420 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'lea'45'slot_420 ~v0 ~v1 ~v2 = du_sim'45'lea'45'slot_420
du_sim'45'lea'45'slot_420 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'lea'45'slot_420 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'lea'45'slot_2796
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-load-code-addr
d_sim'45'load'45'code'45'addr_422 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'load'45'code'45'addr_422 ~v0 ~v1 ~v2
  = du_sim'45'load'45'code'45'addr_422
du_sim'45'load'45'code'45'addr_422 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'code'45'addr_422 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'code'45'addr_2056
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-load-const
d_sim'45'load'45'const_424 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'load'45'const_424 ~v0 ~v1 ~v2
  = du_sim'45'load'45'const_424
du_sim'45'load'45'const_424 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'const_424 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'const_2016
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-load-const-float
d_sim'45'load'45'const'45'float_426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'load'45'const'45'float_426 ~v0 ~v1 ~v2
  = du_sim'45'load'45'const'45'float_426
du_sim'45'load'45'const'45'float_426 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'const'45'float_426 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'const'45'float_2036
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-load-from-slot
d_sim'45'load'45'from'45'slot_428 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_sim'45'load'45'from'45'slot_428 ~v0 ~v1 ~v2
  = du_sim'45'load'45'from'45'slot_428
du_sim'45'load'45'from'45'slot_428 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'from'45'slot_428 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'from'45'slot_898
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-load-indirect
d_sim'45'load'45'indirect_430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_sim'45'load'45'indirect_430 ~v0 ~v1 ~v2
  = du_sim'45'load'45'indirect_430
du_sim'45'load'45'indirect_430 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'indirect_430 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'indirect_848
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-load-indirect-stack
d_sim'45'load'45'indirect'45'stack_432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_sim'45'load'45'indirect'45'stack_432 ~v0 ~v1 ~v2
  = du_sim'45'load'45'indirect'45'stack_432
du_sim'45'load'45'indirect'45'stack_432 ::
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
du_sim'45'load'45'indirect'45'stack_432 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'indirect'45'stack_2832
      v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-load-indirect-suc
d_sim'45'load'45'indirect'45'suc_434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_sim'45'load'45'indirect'45'suc_434 ~v0 ~v1 ~v2
  = du_sim'45'load'45'indirect'45'suc_434
du_sim'45'load'45'indirect'45'suc_434 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'indirect'45'suc_434 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'indirect'45'suc_798
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-load-indirect-suc-stack
d_sim'45'load'45'indirect'45'suc'45'stack_436 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_sim'45'load'45'indirect'45'suc'45'stack_436 ~v0 ~v1 ~v2
  = du_sim'45'load'45'indirect'45'suc'45'stack_436
du_sim'45'load'45'indirect'45'suc'45'stack_436 ::
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
du_sim'45'load'45'indirect'45'suc'45'stack_436 v0 v1 v2 v3 v4 v5 v6
                                               v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'indirect'45'suc'45'stack_2886
      v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-load-tag-lit
d_sim'45'load'45'tag'45'lit_438 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'load'45'tag'45'lit_438 ~v0 ~v1 ~v2
  = du_sim'45'load'45'tag'45'lit_438
du_sim'45'load'45'tag'45'lit_438 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'tag'45'lit_438 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'tag'45'lit_698
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-mov-input2-to-output
d_sim'45'mov'45'input2'45'to'45'output_440 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'mov'45'input2'45'to'45'output_440 ~v0 ~v1 ~v2
  = du_sim'45'mov'45'input2'45'to'45'output_440
du_sim'45'mov'45'input2'45'to'45'output_440 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'mov'45'input2'45'to'45'output_440 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'mov'45'input2'45'to'45'output_664
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-mov-output-to-input2
d_sim'45'mov'45'output'45'to'45'input2_442 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'mov'45'output'45'to'45'input2_442 ~v0 ~v1 ~v2
  = du_sim'45'mov'45'output'45'to'45'input2_442
du_sim'45'mov'45'output'45'to'45'input2_442 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'mov'45'output'45'to'45'input2_442 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'mov'45'output'45'to'45'input2_680
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-mov-to-input
d_sim'45'mov'45'to'45'input_444 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'mov'45'to'45'input_444 ~v0 ~v1 ~v2
  = du_sim'45'mov'45'to'45'input_444
du_sim'45'mov'45'to'45'input_444 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'mov'45'to'45'input_444 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'mov'45'to'45'input_648
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-mov-to-output
d_sim'45'mov'45'to'45'output_446 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'mov'45'to'45'output_446 ~v0 ~v1 ~v2
  = du_sim'45'mov'45'to'45'output_446
du_sim'45'mov'45'to'45'output_446 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'mov'45'to'45'output_446 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'mov'45'to'45'output_632
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-reg-count-inc
d_sim'45'reg'45'count'45'inc_448 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_sim'45'reg'45'count'45'inc_448 ~v0 ~v1 ~v2
  = du_sim'45'reg'45'count'45'inc_448
du_sim'45'reg'45'count'45'inc_448 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'reg'45'count'45'inc_448 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'count'45'inc_2114
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-reg-count-zero
d_sim'45'reg'45'count'45'zero_450 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'reg'45'count'45'zero_450 ~v0 ~v1 ~v2
  = du_sim'45'reg'45'count'45'zero_450
du_sim'45'reg'45'count'45'zero_450 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'reg'45'count'45'zero_450 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'count'45'zero_748
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-reg-scratch-dec
d_sim'45'reg'45'scratch'45'dec_452 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_sim'45'reg'45'scratch'45'dec_452 ~v0 ~v1 ~v2
  = du_sim'45'reg'45'scratch'45'dec_452
du_sim'45'reg'45'scratch'45'dec_452 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'reg'45'scratch'45'dec_452 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'scratch'45'dec_2142
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-reg-scratch-load-count
d_sim'45'reg'45'scratch'45'load'45'count_454 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'reg'45'scratch'45'load'45'count_454 ~v0 ~v1 ~v2
  = du_sim'45'reg'45'scratch'45'load'45'count_454
du_sim'45'reg'45'scratch'45'load'45'count_454 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'reg'45'scratch'45'load'45'count_454 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'scratch'45'load'45'count_764
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-reg-scratch-one
d_sim'45'reg'45'scratch'45'one_456 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'reg'45'scratch'45'one_456 ~v0 ~v1 ~v2
  = du_sim'45'reg'45'scratch'45'one_456
du_sim'45'reg'45'scratch'45'one_456 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'reg'45'scratch'45'one_456 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'scratch'45'one_716
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-reg-scratch-zero
d_sim'45'reg'45'scratch'45'zero_458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'reg'45'scratch'45'zero_458 ~v0 ~v1 ~v2
  = du_sim'45'reg'45'scratch'45'zero_458
du_sim'45'reg'45'scratch'45'zero_458 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'reg'45'scratch'45'zero_458 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'scratch'45'zero_732
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-restore-input
d_sim'45'restore'45'input_460 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_sim'45'restore'45'input_460 ~v0 ~v1 ~v2
  = du_sim'45'restore'45'input_460
du_sim'45'restore'45'input_460 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'restore'45'input_460 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'restore'45'input_1592
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-save-closure-reg
d_sim'45'save'45'closure'45'reg_462 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'save'45'closure'45'reg_462 v0 = coe v0
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-store-at-slot
d_sim'45'store'45'at'45'slot_464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_sim'45'store'45'at'45'slot_464 ~v0 ~v1 ~v2
  = du_sim'45'store'45'at'45'slot_464
du_sim'45'store'45'at'45'slot_464 ::
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
du_sim'45'store'45'at'45'slot_464 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'store'45'at'45'slot_1864
      v2 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-store-indirect
d_sim'45'store'45'indirect_466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_sim'45'store'45'indirect_466 ~v0 ~v1 ~v2
  = du_sim'45'store'45'indirect_466
du_sim'45'store'45'indirect_466 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'store'45'indirect_466 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'store'45'indirect_1494
      v1 v2 v4 v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-store-indirect-stack
d_sim'45'store'45'indirect'45'stack_468 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_sim'45'store'45'indirect'45'stack_468 ~v0 ~v1 ~v2
  = du_sim'45'store'45'indirect'45'stack_468
du_sim'45'store'45'indirect'45'stack_468 ::
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
du_sim'45'store'45'indirect'45'stack_468 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'store'45'indirect'45'stack_2938
      v2 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-store-indirect-suc
d_sim'45'store'45'indirect'45'suc_470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_sim'45'store'45'indirect'45'suc_470 ~v0 ~v1 ~v2
  = du_sim'45'store'45'indirect'45'suc_470
du_sim'45'store'45'indirect'45'suc_470 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'store'45'indirect'45'suc_470 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'store'45'indirect'45'suc_1542
      v1 v2 v4 v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sim-store-indirect-suc-stack
d_sim'45'store'45'indirect'45'suc'45'stack_472 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_sim'45'store'45'indirect'45'suc'45'stack_472 ~v0 ~v1 ~v2
  = du_sim'45'store'45'indirect'45'suc'45'stack_472
du_sim'45'store'45'indirect'45'suc'45'stack_472 ::
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
du_sim'45'store'45'indirect'45'suc'45'stack_472 v0 v1 v2 v3 v4 v5
                                                v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'store'45'indirect'45'suc'45'stack_2994
      v2 v4
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.slot-addr-inj
d_slot'45'addr'45'inj_474 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'inj_474 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.stack-eq
d_stack'45'eq_476 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'eq_476 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_stack'45'eq_458
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.stack-eq-cur
d_stack'45'eq'45'cur_478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_stack'45'eq'45'cur_478 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.stack-eq-win
d_stack'45'eq'45'win_480 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'eq'45'win_480 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.store-dom-written
d_store'45'dom'45'written_482 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_store'45'dom'45'written_482 ~v0 ~v1 ~v2
  = du_store'45'dom'45'written_482
du_store'45'dom'45'written_482 ::
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
du_store'45'dom'45'written_482 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_store'45'dom'45'written_1160
      v1 v4 v5 v6 v7 v8
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.store-heap-eq
d_store'45'heap'45'eq_484 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_store'45'heap'45'eq_484 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.store-slot-heap-eq
d_store'45'slot'45'heap'45'eq_486 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_store'45'slot'45'heap'45'eq_486 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.store-slot-stack-eq
d_store'45'slot'45'stack'45'eq_488 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_store'45'slot'45'stack'45'eq_488 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.sv-tag-zero
d_sv'45'tag'45'zero_490 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sv'45'tag'45'zero_490 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.untouched
d_untouched_492 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched_492 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.untouched-descend
d_untouched'45'descend_494 ::
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
d_untouched'45'descend_494 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.untouched-heap-store
d_untouched'45'heap'45'store_496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_untouched'45'heap'45'store_496 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.untouched-stack-store
d_untouched'45'stack'45'store_498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_untouched'45'stack'45'store_498 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.untouched-write
d_untouched'45'write_500 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_untouched'45'write_500 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.win-at
d_win'45'at_502 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_win'45'at_502 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.win-off
d_win'45'off_504 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_win'45'off_504 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.windows-above
d_windows'45'above_506 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_windows'45'above_506 ~v0 ~v1 ~v2 = du_windows'45'above_506
du_windows'45'above_506 ::
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
du_windows'45'above_506 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_windows'45'above_1350
      v6 v9
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.windows-enc-ext
d_windows'45'enc'45'ext_508 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_windows'45'enc'45'ext_508 ~v0 ~v1 ~v2
  = du_windows'45'enc'45'ext_508
du_windows'45'enc'45'ext_508 ::
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
du_windows'45'enc'45'ext_508 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_windows'45'enc'45'ext_2600
      v8 v10
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.windows-heap-store
d_windows'45'heap'45'store_510 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_windows'45'heap'45'store_510 ~v0 ~v1 ~v2
  = du_windows'45'heap'45'store_510
du_windows'45'heap'45'store_510 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'heap'45'store_510 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_windows'45'heap'45'store_1470
      v1 v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.windows-leave
d_windows'45'leave_512 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_windows'45'leave_512 v0 ~v1 ~v2 = du_windows'45'leave_512 v0
du_windows'45'leave_512 ::
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
du_windows'45'leave_512 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_windows'45'leave_1284
      (coe v0) v4 v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.windows-reanchor
d_windows'45'reanchor_514 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_windows'45'reanchor_514 ~v0 ~v1 ~v2 = du_windows'45'reanchor_514
du_windows'45'reanchor_514 ::
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
du_windows'45'reanchor_514 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_windows'45'reanchor_1256
      v8 v9
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.windows-slot-store
d_windows'45'slot'45'store_516 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_windows'45'slot'45'store_516 ~v0 ~v1 ~v2
  = du_windows'45'slot'45'store_516
du_windows'45'slot'45'store_516 ::
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
du_windows'45'slot'45'store_516 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_windows'45'slot'45'store_1796
      v8 v10
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.windows-write-below
d_windows'45'write'45'below_518 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_windows'45'write'45'below_518 ~v0 ~v1 ~v2
  = du_windows'45'write'45'below_518
du_windows'45'write'45'below_518 ::
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
du_windows'45'write'45'below_518 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_windows'45'write'45'below_1428
      v6
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.≡ᵇ-refl
d_'8801''7495''45'refl_520 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_520 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.≢→≡ᵇfalse
d_'8802''8594''8801''7495'false_522 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8802''8594''8801''7495'false_522 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.dom-fresh
d_dom'45'fresh_532 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'fresh_532 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'fresh_436
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.dom-sized
d_dom'45'sized_534 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_dom'45'sized_534 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'sized_446
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.dom-written
d_dom'45'written_536 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_dom'45'written_536 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'written_442
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.halt-eq
d_halt'45'eq_538 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45'eq_538 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.heap-eq
d_heap'45'eq_540 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'eq_540 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.lo-le
d_lo'45'le_542 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'le_542 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_lo'45'le_452
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.r14-eq
d_r14'45'eq_544 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r14'45'eq_544 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.r15-eq
d_r15'45'eq_546 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r15'45'eq_546 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.rax-eq
d_rax'45'eq_548 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rax'45'eq_548 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.rbx-eq
d_rbx'45'eq_550 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rbx'45'eq_550 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.rdi-eq
d_rdi'45'eq_552 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45'eq_552 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.rsi-eq
d_rsi'45'eq_554 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rsi'45'eq_554 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.rsp-eq
d_rsp'45'eq_556 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rsp'45'eq_556 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.stack-eq
d_stack'45'eq_558 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'eq_558 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_stack'45'eq_458
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.FlatCorr.untouched
d_untouched_560 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched_560 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.HeapView.HDom
d_HDom_564 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> ()
d_HDom_564 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.HeapView.dom-below
d_dom'45'below_566 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_566 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'below_262
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.HeapView.front-lo
d_front'45'lo_568 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo_568 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_front'45'lo_266
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.HeapView.haddr
d_haddr_570 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_haddr_570 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_haddr_244
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.HeapView.haddr-inj
d_haddr'45'inj_572 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_572 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.HeapView.haddr-suc
d_haddr'45'suc_574 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_574 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.HeapView.hfront
d_hfront_576 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer
d_hfront_576 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_hfront_248
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.C.HeapView.lo
d_lo_578 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer
d_lo_578 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_lo_264
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.CompiledCorr.dataCorr
d_dataCorr_582 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dataCorr_582 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.d_dataCorr_524
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.CompiledCorr.pc-off
d_pc'45'off_584 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pc'45'off_584 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.FlatWF
d_FlatWF_588 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_FlatWF_588 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.sv-below
d_sv'45'below_592 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_sv'45'below_592 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.FlatRegTag
d_FlatRegTag_606 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_FlatRegTag_606 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.x86-len
d_x86'45'len_630 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Integer
d_x86'45'len_630 ~v0 ~v1 ~v2 = du_x86'45'len_630
du_x86'45'len_630 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Integer
du_x86'45'len_630
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatComposition.du_x86'45'len_156
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.StackPtrOK
d_StackPtrOK_646 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_StackPtrOK_646 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.StackPtrWF
d_StackPtrWF_650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_StackPtrWF_650 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.PtrB
d_PtrB_662 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_PtrB_662 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.PtrBoundsWF
d_PtrBoundsWF_666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_PtrBoundsWF_666 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.Meets
d_Meets_684 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_Meets_684 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.nonhalt-noncall
d_nonhalt'45'noncall_702 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_nonhalt'45'noncall_702 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.t≢f
d_t'8802'f_864 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_t'8802'f_864 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.n≢j
d_n'8802'j_870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8802'j_870 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.Emitted
d_Emitted_874 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] -> ()
d_Emitted_874 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.EntryLike
d_EntryLike_876 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_EntryLike_876 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.Reachable
d_Reachable_878 a0 a1 a2 a3 a4 a5 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.RunAt
d_RunAt_880 a0 a1 a2 a3 a4 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.run-emit
d_run'45'emit_890 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'emit_890 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.run-emitted
d_run'45'emitted_892 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'emitted_892 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'ir_218
         (coe v0))
      erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.run-heap
d_run'45'heap_894 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  AgdaAny
d_run'45'heap_894 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'heap_222
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.run-ir
d_run'45'ir_896 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_run'45'ir_896 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'ir_218
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.run-reach
d_run'45'reach_898 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178
d_run'45'reach_898 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'reach_224
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.RunAt.run-emit
d_run'45'emit_908 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'emit_908 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.RunAt.run-heap
d_run'45'heap_910 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  AgdaAny
d_run'45'heap_910 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'heap_222
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.RunAt.run-ir
d_run'45'ir_912 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_run'45'ir_912 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'ir_218
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.RunAt.run-reach
d_run'45'reach_914 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178
d_run'45'reach_914 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'reach_224
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.FlatInv
d_FlatInv_924 a0 a1 a2 a3 a4 a5 a6 = ()
data T_FlatInv_924
  = C_mkFlatInv_954 MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506
                    MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_314
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.FlatInv.inv-wf
d_inv'45'wf_944 ::
  T_FlatInv_924 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506
d_inv'45'wf_944 v0
  = case coe v0 of
      C_mkFlatInv_954 v1 v2 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.FlatInv.inv-regtag
d_inv'45'regtag_946 ::
  T_FlatInv_924 ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_314
d_inv'45'regtag_946 v0
  = case coe v0 of
      C_mkFlatInv_954 v1 v2 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.FlatInv.inv-ev
d_inv'45'ev_948 ::
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv'45'ev_948 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.FlatInv.inv-env
d_inv'45'env_950 ::
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv'45'env_950 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.FlatInv.inv-run
d_inv'45'run_952 ::
  T_FlatInv_924 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204
d_inv'45'run_952 v0
  = case coe v0 of
      C_mkFlatInv_954 v1 v2 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.frame-op-absurd
d_frame'45'op'45'absurd_964 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_frame'45'op'45'absurd_964 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8
  = du_frame'45'op'45'absurd_964 v4 v6 v7
du_frame'45'op'45'absurd_964 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> AgdaAny
du_frame'45'op'45'absurd_964 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.FrameFreeTrace.du_fetch'45'frame'45'free_700
             (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
             (coe MAlonzo.Code.Once.IRTy.C_Unit_16) v3 v2
             (MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v0)) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.flat-inv-step
d_flat'45'inv'45'step_986 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> T_FlatInv_924
d_flat'45'inv'45'step_986 v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 ~v8 ~v9 v10
  = du_flat'45'inv'45'step_986 v0 v5 v6 v7 v10
du_flat'45'inv'45'step_986 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatInv_924 -> T_FlatInv_924
du_flat'45'inv'45'step_986 v0 v1 v2 v3 v4
  = coe
      C_mkFlatInv_954
      (MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_flat'45'wf'45'step_2064
         (coe v0) (coe v1) (coe v2) (coe v3) (coe d_inv'45'wf_944 (coe v4)))
      (MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.d_flat'45'regtag'45'step_1406
         (coe v0) (coe v1) (coe v2) (coe v3)
         (coe d_inv'45'regtag_946 (coe v4)))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_mkRunAt_226
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'ir_218
            (coe d_inv'45'run_952 (coe v4)))
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'heap_222
            (coe d_inv'45'run_952 (coe v4)))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_reach'45'step_192
            v1 v3
            (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'reach_224
               (coe d_inv'45'run_952 (coe v4)))))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.above-frontier-disj
d_above'45'frontier'45'disj_1006 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_above'45'frontier'45'disj_1006 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.slot-heap-disj
d_slot'45'heap'45'disj_1030 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_slot'45'heap'45'disj_1030 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.block-run-exec
d_block'45'run'45'exec_1056 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_block'45'run'45'exec_1056 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.event-of
d_event'45'of_1286 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_event'45'of_1286 ~v0 ~v1 ~v2 = du_event'45'of_1286
du_event'45'of_1286 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_event'45'of_1286
  = coe MAlonzo.Code.Once.Adequacy.FlatEvents.du_event'45'of_280
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.flat-events
d_flat'45'events_1288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'events_1288 v0 ~v1 ~v2 = du_flat'45'events_1288 v0
du_flat'45'events_1288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_flat'45'events_1288 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_286 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.flat-events-fetch
d_flat'45'events'45'fetch_1290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'events'45'fetch_1290 v0 ~v1 ~v2
  = du_flat'45'events'45'fetch_1290 v0
du_flat'45'events'45'fetch_1290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_flat'45'events'45'fetch_1290 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events'45'fetch_290
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.flat-events-step
d_flat'45'events'45'step_1294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'events'45'step_1294 v0 ~v1 ~v2
  = du_flat'45'events'45'step_1294 v0
du_flat'45'events'45'step_1294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_flat'45'events'45'step_1294 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events'45'step_288
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.fetch-nothing-drop
d_fetch'45'nothing'45'drop_1300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'nothing'45'drop_1300 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.fetch-just-drop
d_fetch'45'just'45'drop_1324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'just'45'drop_1324 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.sigop-concrete-fetch
d_sigop'45'concrete'45'fetch_1364 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_sigop'45'concrete'45'fetch_1364 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.sigop-run-arith
d_sigop'45'run'45'arith_1404 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_sigop'45'run'45'arith_1404 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.execInstr-cmp-mi
d_execInstr'45'cmp'45'mi_1438 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Mem_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_execInstr'45'cmp'45'mi_1438 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.event-of-pure
d_event'45'of'45'pure_1462 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_event'45'of'45'pure_1462 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.store-guard
d_store'45'guard_1478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'guard_1478 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go
d_go_1490 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_1490 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.slot-empty-stop
d_slot'45'empty'45'stop_1558 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_slot'45'empty'45'stop_1558 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                             ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_slot'45'empty'45'stop_1558
du_slot'45'empty'45'stop_1558 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_slot'45'empty'45'stop_1558
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
      erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.dc
d_dc_1600 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_dc_1600 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_dc_1600 v13
du_dc_1600 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_1600 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.d_dataCorr_524
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.halt-s
d_halt'45's_1602 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_halt'45's_1602 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.fetch-x86
d_fetch'45'x86_1604 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_fetch'45'x86_1604 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.rd
d_rd_1608 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_rd_1608 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.stuck
d_stuck_1610 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_stuck_1610 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.result
d_result_1616 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_result_1616 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.sigop-run-external
d_sigop'45'run'45'external_1642 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_sigop'45'run'45'external_1642 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.events-running-end
d_events'45'running'45'end_1682 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_events'45'running'45'end_1682 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                ~v9 ~v10 ~v11 ~v12 ~v13
  = du_events'45'running'45'end_1682
du_events'45'running'45'end_1682 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_events'45'running'45'end_1682
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
      erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.cfetch-nothing
d_cfetch'45'nothing_1710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cfetch'45'nothing_1710 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.events-running-call
d_events'45'running'45'call_1732
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.events-running-call"
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.events-running-thunk
d_events'45'running'45'thunk_1754
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.events-running-thunk"
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.events-running-ret
d_events'45'running'45'ret_1774
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.events-running-ret"
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.emitted-shape-check
d_emitted'45'shape'45'check_1780
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.emitted-shape-check"
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.run-meets
d_run'45'meets_1788
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.run-meets"
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.arith-sigop-contract
d_arith'45'sigop'45'contract_1808
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.arith-sigop-contract"
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.external-sigop-contract
d_external'45'sigop'45'contract_1828
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.external-sigop-contract"
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.fetch≡lookup
d_fetch'8801'lookup_1834 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'8801'lookup_1834 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.emitted-slot-below-budget
d_emitted'45'slot'45'below'45'budget_1854 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_emitted'45'slot'45'below'45'budget_1854 ~v0 ~v1 ~v2 v3 v4 ~v5 v6
                                          ~v7 ~v8
  = du_emitted'45'slot'45'below'45'budget_1854 v3 v4 v6
du_emitted'45'slot'45'below'45'budget_1854 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_emitted'45'slot'45'below'45'budget_1854 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotBudget.du_emitted'45'slot'45'seg_2218
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.ff→seg-id
d_ff'8594'seg'45'id_1870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ff'8594'seg'45'id_1870 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.RetMatch
d_RetMatch_1876 a0 a1 a2 a3 a4 a5 a6 = ()
data T_RetMatch_1876
  = C_rm'45''91''93'_1882 | C_rm'45''8759'_1894 T_RetMatch_1876
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.SegWF
d_SegWF_1902 a0 a1 a2 a3 a4 a5 = ()
newtype T_SegWF_1902 = C_mkSegWF_1918 T_RetMatch_1876
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.SegWF.seg-cur
d_seg'45'cur_1914 ::
  T_SegWF_1902 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'cur_1914 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.SegWF.seg-stack
d_seg'45'stack_1916 :: T_SegWF_1902 -> T_RetMatch_1876
d_seg'45'stack_1916 v0
  = case coe v0 of
      C_mkSegWF_1918 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.dj-aux
d_dj'45'aux_1926 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_dj'45'aux_1926 ~v0 ~v1 ~v2 v3 ~v4 = du_dj'45'aux_1926 v3
du_dj'45'aux_1926 ::
  Maybe Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_dj'45'aux_1926 v0
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
d_db'45'aux_1944 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_db'45'aux_1944 v0 ~v1 ~v2 v3 v4 v5 ~v6
  = du_db'45'aux_1944 v0 v3 v4 v5
du_db'45'aux_1944 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_db'45'aux_1944 v0 v1 v2 v3
  = if coe v1
      then coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                du_dj'45'aux_1926
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v0)
                   (coe v3) (coe v2)))
      else coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.JumpPost
d_JumpPost_1966 a0 a1 a2 a3 a4 a5 a6 = ()
data T_JumpPost_1966
  = C_jp'45'suc_1976 | C_jp'45'halt_1978 | C_jp'45'to_1982 Integer
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.PcView
d_PcView_1986 a0 a1 a2 a3 = ()
data T_PcView_1986
  = C_pv'45'suc_1994 AgdaAny |
    C_pv'45'jump_2002 AgdaAny Integer
                      ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
                       T_JumpPost_1966) |
    C_pv'45'thunk_2008 Integer Integer | C_pv'45'ret_2012 Integer
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.pcView
d_pcView_2016 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  AgdaAny -> T_PcView_1986
d_pcView_2016 v0 ~v1 ~v2 v3 ~v4 = du_pcView_2016 v0 v3
du_pcView_2016 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  T_PcView_1986
du_pcView_2016 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2194
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2196
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202 v2
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204 v2
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2212 v2
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2218 v2
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2224
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2226 v2
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2228 v2
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2230 v2
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2232 v2
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2238 v2 v3 v4
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2242 v2 v3 v4
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2244 v2
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2246
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2248 v2
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252 v2
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256 v2
        -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258 v2
        -> case coe v2 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176 v3
               -> coe C_pv'45'suc_1994 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178 v3
               -> coe
                    C_pv'45'jump_2002 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) v3
                    (\ v4 v5 -> coe du_go_2032 (coe v0) (coe v3) v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180 v3
               -> coe
                    C_pv'45'jump_2002 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) v3
                    (coe du_go_2064 (coe v0) (coe v3))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182 v3
               -> coe
                    C_pv'45'jump_2002 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) v3
                    (coe du_go_2096 (coe v0) (coe v3))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2184 v3 v4
               -> coe C_pv'45'thunk_2008 v3 v4
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2186 v3
               -> coe C_pv'45'ret_2012 v3
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go
d_go_2032 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_JumpPost_1966
d_go_2032 v0 ~v1 ~v2 v3 ~v4 v5 ~v6 = du_go_2032 v0 v3 v5
du_go_2032 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_JumpPost_1966
du_go_2032 v0 v1 v2
  = coe
      du_mk_2044
      (coe
         du_dj'45'aux_1926
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v0)
            (coe v2) (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.mk
d_mk_2044 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_JumpPost_1966
d_mk_2044 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_mk_2044 v7
du_mk_2044 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_JumpPost_1966
du_mk_2044 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe C_jp'45'halt_1978
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> coe seq (coe v3) (coe C_jp'45'to_1982 v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go
d_go_2064 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_JumpPost_1966
d_go_2064 v0 ~v1 ~v2 v3 ~v4 v5 v6 = du_go_2064 v0 v3 v5 v6
du_go_2064 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_JumpPost_1966
du_go_2064 v0 v1 v2 v3
  = coe
      du_mk_2074
      (coe
         du_db'45'aux_1944 (coe v0)
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
d_mk_2074 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_JumpPost_1966
d_mk_2074 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_mk_2074 v7
du_mk_2074 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_JumpPost_1966
du_mk_2074 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe C_jp'45'suc_1976
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
               -> coe C_jp'45'halt_1978
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                      -> coe seq (coe v4) (coe C_jp'45'to_1982 v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go
d_go_2096 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_JumpPost_1966
d_go_2096 v0 ~v1 ~v2 v3 ~v4 v5 v6 = du_go_2096 v0 v3 v5 v6
du_go_2096 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_JumpPost_1966
du_go_2096 v0 v1 v2 v3
  = coe
      du_mk_2106
      (coe
         du_db'45'aux_1944 (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_96
            (coe
               MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_108
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3))))
         (coe v1) (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.mk
d_mk_2106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_JumpPost_1966
d_mk_2106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_mk_2106 v7
du_mk_2106 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_JumpPost_1966
du_mk_2106 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe C_jp'45'suc_1976
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
               -> coe C_jp'45'halt_1978
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                      -> coe seq (coe v4) (coe C_jp'45'to_1982 v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.run-seg-wf
d_run'45'seg'45'wf_2226 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  T_SegWF_1902
d_run'45'seg'45'wf_2226 v0 ~v1 v2 v3 v4 v5
  = du_run'45'seg'45'wf_2226 v0 v2 v3 v4 v5
du_run'45'seg'45'wf_2226 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  T_SegWF_1902
du_run'45'seg'45'wf_2226 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_mkRunAt_226 v5 v7 v8
        -> coe
             du_go_2248 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5) (coe v7)
             (coe v8) (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.B₀
d_B'8320'_2244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotBudget.T_SegState_160
d_B'8320'_2244 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_B'8320'_2244 v5
du_B'8320'_2244 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotBudget.T_SegState_160
du_B'8320'_2244 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotBudget.C_mkSeg_170
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_700
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v0))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go
d_go_2248 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  T_SegWF_1902
d_go_2248 v0 ~v1 v2 v3 v4 v5 ~v6 v7 v8 ~v9 v10
  = du_go_2248 v0 v2 v3 v4 v5 v7 v8 v10
du_go_2248 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  T_SegWF_1902
du_go_2248 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_reach'45'start_186 v9
        -> coe C_mkSegWF_1918 (coe C_rm'45''91''93'_1882)
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_reach'45'step_192 v8 v9 v10
        -> coe
             du_step_2280 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v6) (coe v9) (coe v10) (coe du_pcView_2016 (coe v0) (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.em
d_em_2272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_em_2272 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 ~v8 ~v9 v10 ~v11 ~v12 ~v13
  = du_em_2272 v5 v6 v7 v10
du_em_2272 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> AgdaAny
du_em_2272 v0 v1 v2 v3
  = coe
      du_frame'45'op'45'absurd_964 (coe v3)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1))
      (coe v2)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.ih
d_ih_2274 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_SegWF_1902
d_ih_2274 v0 ~v1 v2 v3 v4 v5 ~v6 v7 v8 ~v9 v10 v11 ~v12 ~v13
  = du_ih_2274 v0 v2 v3 v4 v5 v7 v8 v10 v11
du_ih_2274 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  T_SegWF_1902
du_ih_2274 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_go_2248 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v8)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.lk
d_lk_2276 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lk_2276 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.seg-suc
d_seg'45'suc_2278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'suc_2278 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.step
d_step_2280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_PcView_1986 -> T_SegWF_1902
d_step_2280 v0 ~v1 v2 v3 v4 v5 ~v6 v7 v8 ~v9 v10 v11 ~v12 ~v13 v14
  = du_step_2280 v0 v2 v3 v4 v5 v7 v8 v10 v11 v14
du_step_2280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  T_PcView_1986 -> T_SegWF_1902
du_step_2280 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      C_pv'45'suc_1994 v10
        -> coe
             C_mkSegWF_1918
             (d_seg'45'stack_1916
                (coe
                   du_ih_2274 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                   (coe v6) (coe v7) (coe v8)))
      C_pv'45'jump_2002 v10 v11 v13
        -> coe
             C_mkSegWF_1918
             (d_seg'45'stack_1916
                (coe
                   du_ih_2274 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                   (coe v6) (coe v7) (coe v8)))
      C_pv'45'thunk_2008 v10 v11
        -> coe
             C_mkSegWF_1918
             (d_seg'45'stack_1916
                (coe
                   du_ih_2274 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                   (coe v6) (coe v7) (coe v8)))
      C_pv'45'ret_2012 v10
        -> coe
             du_ret'45'step_2366 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._._.same
d_same_2290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackSlot.T_SameFrames_310
d_same_2290 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._._.stable
d_stable_2292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stable_2292 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._._.same
d_same_2308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   T_JumpPost_1966) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackSlot.T_SameFrames_310
d_same_2308 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._._.lkm
d_lkm_2310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   T_JumpPost_1966) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lkm_2310 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._._.jgo
d_jgo_2312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   T_JumpPost_1966) ->
  T_JumpPost_1966 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_jgo_2312 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._._.pc-eq
d_pc'45'eq_2346 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pc'45'eq_2346 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._._.step-eq
d_step'45'eq_2348 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'eq_2348 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._._.ret-step
d_ret'45'step_2366 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_SegWF_1902
d_ret'45'step_2366 v0 ~v1 v2 v3 v4 v5 ~v6 v7 v8 ~v9 v10 v11 ~v12
                   ~v13 ~v14 ~v15 ~v16
  = du_ret'45'step_2366 v0 v2 v3 v4 v5 v7 v8 v10 v11
du_ret'45'step_2366 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  T_SegWF_1902
du_ret'45'step_2366 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_go'45'rm_2376
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v7))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v7)))
      (coe
         d_seg'45'stack_1916
         (coe
            du_ih_2274 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v6) (coe v7) (coe v8)))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._._._.go-rm
d_go'45'rm_2376 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [Integer] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_RetMatch_1876 -> T_SegWF_1902
d_go'45'rm_2376 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 ~v13 ~v14 v15 v16 ~v17 ~v18 v19
  = du_go'45'rm_2376 v15 v16 v19
du_go'45'rm_2376 ::
  [Integer] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_RetMatch_1876 -> T_SegWF_1902
du_go'45'rm_2376 v0 v1 v2
  = case coe v0 of
      []
        -> coe
             seq (coe v1)
             (coe seq (coe v2) (coe C_mkSegWF_1918 (coe C_rm'45''91''93'_1882)))
      (:) v3 v4
        -> case coe v1 of
             (:) v5 v6
               -> coe
                    seq (coe v5)
                    (case coe v2 of
                       C_rm'45''8759'_1894 v13 -> coe C_mkSegWF_1918 v13
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.stack-ptr-step
d_stack'45'ptr'45'step_2428 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_320 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_320
d_stack'45'ptr'45'step_2428 v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8 v9
  = du_stack'45'ptr'45'step_2428 v0 v3 v4 v5 v9
du_stack'45'ptr'45'step_2428 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_320 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_320
du_stack'45'ptr'45'step_2428 v0 v1 v2 v3 v4
  = coe
      seq (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.du_flat'45'stack'45'ptr_1564
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.entry-stack-ptr
d_entry'45'stack'45'ptr_2860 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_320
d_entry'45'stack'45'ptr_2860 ~v0 ~v1 ~v2 v3 v4
  = du_entry'45'stack'45'ptr_2860 v3 v4
du_entry'45'stack'45'ptr_2860 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_320
du_entry'45'stack'45'ptr_2860 v0 v1
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
                                                                  du_go_2878
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
d_go_2878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_go_2878 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 v14 ~v15
  = du_go_2878 v14
du_go_2878 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
du_go_2878 v0
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
d_entry'45'ptr'45'bounds_2928 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_360
d_entry'45'ptr'45'bounds_2928 ~v0 ~v1 ~v2 v3 v4
  = du_entry'45'ptr'45'bounds_2928 v3 v4
du_entry'45'ptr'45'bounds_2928 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_360
du_entry'45'ptr'45'bounds_2928 v0 v1
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
                                                                  du_go_2946
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
d_go_2946 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_go_2946 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 v14 ~v15
  = du_go_2946 v14
du_go_2946 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
du_go_2946 v0
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
d_entry'45'flat'45'wf_2996 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506
d_entry'45'flat'45'wf_2996 ~v0 ~v1 ~v2 v3 v4
  = du_entry'45'flat'45'wf_2996 v3 v4
du_entry'45'flat'45'wf_2996 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506
du_entry'45'flat'45'wf_2996 v0 v1
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
                                                               du_go_3014
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
d_go_3014 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
d_go_3014 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 v14 ~v15
  = du_go_3014 v14
du_go_3014 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> AgdaAny
du_go_3014 v0
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
d_run'45'stack'45'ptr_3072 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_320
d_run'45'stack'45'ptr_3072 v0 ~v1 ~v2 v3 v4 v5
  = du_run'45'stack'45'ptr_3072 v0 v3 v4 v5
du_run'45'stack'45'ptr_3072 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_320
du_run'45'stack'45'ptr_3072 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_mkRunAt_226 v4 v6 v7
        -> coe du_go_3092 (coe v0) (coe v1) (coe v2) (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go
d_go_3092 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_320
d_go_3092 v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_go_3092 v0 v3 v9 v10
du_go_3092 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_320
du_go_3092 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_reach'45'start_186 v5
        -> coe du_entry'45'stack'45'ptr_2860 (coe v2) (coe v5)
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_reach'45'step_192 v4 v5 v6
        -> coe
             du_stack'45'ptr'45'step_2428 (coe v0) (coe v4) (coe v1) (coe v5)
             (coe du_go_3092 (coe v0) (coe v1) (coe v5) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.stack-ptr-current
d_stack'45'ptr'45'current_3116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'ptr'45'current_3116 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_stack'45'ptr'45'current_3116
du_stack'45'ptr'45'current_3116 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stack'45'ptr'45'current_3116
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.stack-ptr-current-suc
d_stack'45'ptr'45'current'45'suc_3138 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'ptr'45'current'45'suc_3138 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      ~v7 ~v8
  = du_stack'45'ptr'45'current'45'suc_3138
du_stack'45'ptr'45'current'45'suc_3138 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stack'45'ptr'45'current'45'suc_3138
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.slot-read-in-frame
d_slot'45'read'45'in'45'frame_3160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'read'45'in'45'frame_3160 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 ~v8
                                   ~v9
  = du_slot'45'read'45'in'45'frame_3160 v4 v5 v7
du_slot'45'read'45'in'45'frame_3160 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'read'45'in'45'frame_3160 v0 v1 v2
  = coe
      du_emitted'45'slot'45'below'45'budget_1854
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'ir_218
         (coe v2))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v0)) (coe v1)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.emitted-alloc-min
d_emitted'45'alloc'45'min_3188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_emitted'45'alloc'45'min_3188 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7
  = du_emitted'45'alloc'45'min_3188 v4 v6
du_emitted'45'alloc'45'min_3188 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_emitted'45'alloc'45'min_3188 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.AllocMin.du_fetch'45'alloc'45'min_628
             (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
             (coe MAlonzo.Code.Once.IRTy.C_Unit_16) v2
             (MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v0)) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.ptr-bounds-step
d_ptr'45'bounds'45'step_3204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_360 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_360
d_ptr'45'bounds'45'step_3204 v0 ~v1 ~v2 v3 v4 v5 v6 ~v7 v8 v9 v10
  = du_ptr'45'bounds'45'step_3204 v0 v3 v4 v5 v6 v8 v9 v10
du_ptr'45'bounds'45'step_3204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_360 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_360
du_ptr'45'bounds'45'step_3204 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v8 v9 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v8 v9 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2194
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v8 v9 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2196
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v8 v9 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v8 v9 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v8 v9 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202 v8
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204 v8
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v8 v9 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v8 v9 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2210 v8
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2212 v8
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2218 v8
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2224
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v8 v9 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2226 v8
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2228 v8
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2230 v8
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2232 v8
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2238 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v11 v12 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2242 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v11 v12 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2244 v8
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2246
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v8 v9 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2248 v8
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252 v8
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe
                (\ v9 v10 ->
                   coe
                     du_emitted'45'alloc'45'min_3188 (coe v3)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'ir_218
                           (coe v4))
                        erased)))
             (coe v6) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256 v8
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258 v8
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_1788
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v6)
             (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.run-wf-ptr-bounds
d_run'45'wf'45'ptr'45'bounds_3762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'wf'45'ptr'45'bounds_3762 v0 ~v1 ~v2 v3 v4 v5
  = du_run'45'wf'45'ptr'45'bounds_3762 v0 v3 v4 v5
du_run'45'wf'45'ptr'45'bounds_3762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'wf'45'ptr'45'bounds_3762 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_mkRunAt_226 v4 v6 v7
        -> coe
             du_go_3782 (coe v0) (coe v1) (coe v4) erased (coe v6) (coe v2)
             (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go
d_go_3782 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_3782 v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 ~v8 v9 v10
  = du_go_3782 v0 v3 v5 v6 v7 v9 v10
du_go_3782 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_Reachable_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_3782 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_reach'45'start_186 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_entry'45'flat'45'wf_2996 (coe v5) (coe v8))
             (coe du_entry'45'ptr'45'bounds_2928 (coe v5) (coe v8))
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_reach'45'step_192 v7 v8 v9
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_flat'45'wf'45'step_2064
                (coe v0) (coe v7) (coe v1) (coe v8)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_go_3782 (coe v0) (coe v1) (coe v2) erased (coe v4) (coe v8)
                      (coe v9))))
             (coe
                du_ptr'45'bounds'45'step_3204 (coe v0) (coe v7) (coe v1) (coe v8)
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_mkRunAt_226
                   v2 v4 v9)
                (coe
                   du_frame'45'op'45'absurd_964 (coe v8)
                   (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3))
                   (coe v4))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_go_3782 (coe v0) (coe v1) (coe v2) erased (coe v4) (coe v8)
                      (coe v9)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      du_go_3782 (coe v0) (coe v1) (coe v2) erased (coe v4) (coe v8)
                      (coe v9))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.run-ptr-bounds
d_run'45'ptr'45'bounds_3806 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_360
d_run'45'ptr'45'bounds_3806 v0 ~v1 ~v2 v3 v4 v5
  = du_run'45'ptr'45'bounds_3806 v0 v3 v4 v5
du_run'45'ptr'45'bounds_3806 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_360
du_run'45'ptr'45'bounds_3806 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         du_run'45'wf'45'ptr'45'bounds_3762 (coe v0) (coe v1) (coe v2)
         (coe v3))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.run-shape-check
d_run'45'shape'45'check_3822 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'shape'45'check_3822 v0 ~v1 v2 ~v3 ~v4 v5
  = du_run'45'shape'45'check_3822 v0 v2 v5
du_run'45'shape'45'check_3822 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'shape'45'check_3822 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe du_chk_3834 (coe v0) (coe v1) (coe v2)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe du_chk_3834 (coe v0) (coe v1) (coe v2)))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.chk
d_chk_3834 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_chk_3834 v0 ~v1 v2 ~v3 ~v4 v5 = du_chk_3834 v0 v2 v5
du_chk_3834 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_chk_3834 v0 v1 v2
  = coe
      d_emitted'45'shape'45'check_1780 v0 erased v1
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'ir_218
         (coe v2))
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.d_run'45'heap_222
         (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.load-indirect-target-ptr
d_load'45'indirect'45'target'45'ptr_3844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'target'45'ptr_3844 v0 ~v1 v2 v3 v4 v5 ~v6
  = du_load'45'indirect'45'target'45'ptr_3844 v0 v2 v3 v4 v5
du_load'45'indirect'45'target'45'ptr_3844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'target'45'ptr_3844 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.du_site'45'load'45'ptr_2284
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_e'45'in1_34
         (coe du_st_3864 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_run'45'meets_1788 v0 erased v1 v2 v3 v4
            (coe du_env_3860 (coe v0) (coe v1) (coe v4)) erased))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.sc
d_sc_3858 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sc_3858 v0 ~v1 v2 ~v3 ~v4 v5 ~v6 = du_sc_3858 v0 v2 v5
du_sc_3858 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sc_3858 v0 v1 v2
  = coe du_run'45'shape'45'check_3822 (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.env
d_env_3860 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
d_env_3860 v0 ~v1 v2 ~v3 ~v4 v5 ~v6 = du_env_3860 v0 v2 v5
du_env_3860 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  Integer -> MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
du_env_3860 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_sc_3858 (coe v0) (coe v1) (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.chk
d_chk_3862 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chk_3862 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.st
d_st_3864 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
d_st_3864 v0 ~v1 v2 v3 v4 v5 ~v6 = du_st_3864 v0 v2 v3 v4 v5
du_st_3864 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
du_st_3864 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_state'45'at_980
      (coe du_env_3860 (coe v0) (coe v1) (coe v4))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_entry'45'expect_962
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
      (coe v2) (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v3))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.ok
d_ok_3866 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok_3866 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.load-indirect-suc-target-ptr
d_load'45'indirect'45'suc'45'target'45'ptr_3874 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'target'45'ptr_3874 v0 ~v1 v2 v3 v4 v5
                                                ~v6
  = du_load'45'indirect'45'suc'45'target'45'ptr_3874 v0 v2 v3 v4 v5
du_load'45'indirect'45'suc'45'target'45'ptr_3874 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'target'45'ptr_3874 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.du_site'45'load'45'ptr_2284
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_e'45'in1_34
         (coe du_st_3894 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_run'45'meets_1788 v0 erased v1 v2 v3 v4
            (coe du_env_3890 (coe v0) (coe v1) (coe v4)) erased))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.sc
d_sc_3888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sc_3888 v0 ~v1 v2 ~v3 ~v4 v5 ~v6 = du_sc_3888 v0 v2 v5
du_sc_3888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sc_3888 v0 v1 v2
  = coe du_run'45'shape'45'check_3822 (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.env
d_env_3890 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
d_env_3890 v0 ~v1 v2 ~v3 ~v4 v5 ~v6 = du_env_3890 v0 v2 v5
du_env_3890 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  Integer -> MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
du_env_3890 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_sc_3888 (coe v0) (coe v1) (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.chk
d_chk_3892 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chk_3892 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.st
d_st_3894 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
d_st_3894 v0 ~v1 v2 v3 v4 v5 ~v6 = du_st_3894 v0 v2 v3 v4 v5
du_st_3894 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
du_st_3894 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_state'45'at_980
      (coe du_env_3890 (coe v0) (coe v1) (coe v4))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_entry'45'expect_962
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
      (coe v2) (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v3))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.ok
d_ok_3896 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok_3896 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.store-indirect-target-ptr
d_store'45'indirect'45'target'45'ptr_3904 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_store'45'indirect'45'target'45'ptr_3904 v0 ~v1 v2 v3 v4 v5 ~v6
  = du_store'45'indirect'45'target'45'ptr_3904 v0 v2 v3 v4 v5
du_store'45'indirect'45'target'45'ptr_3904 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_store'45'indirect'45'target'45'ptr_3904 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.du_site'45'store'45'ptr_3060
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_e'45'in1_34
         (coe du_st_3924 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_run'45'meets_1788 v0 erased v1 v2 v3 v4
            (coe du_env_3920 (coe v0) (coe v1) (coe v4)) erased))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.sc
d_sc_3918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sc_3918 v0 ~v1 v2 ~v3 ~v4 v5 ~v6 = du_sc_3918 v0 v2 v5
du_sc_3918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sc_3918 v0 v1 v2
  = coe du_run'45'shape'45'check_3822 (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.env
d_env_3920 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
d_env_3920 v0 ~v1 v2 ~v3 ~v4 v5 ~v6 = du_env_3920 v0 v2 v5
du_env_3920 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  Integer -> MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
du_env_3920 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_sc_3918 (coe v0) (coe v1) (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.chk
d_chk_3922 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chk_3922 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.st
d_st_3924 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
d_st_3924 v0 ~v1 v2 v3 v4 v5 ~v6 = du_st_3924 v0 v2 v3 v4 v5
du_st_3924 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
du_st_3924 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_state'45'at_980
      (coe du_env_3920 (coe v0) (coe v1) (coe v4))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_entry'45'expect_962
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
      (coe v2) (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v3))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.ok
d_ok_3926 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok_3926 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.store-indirect-suc-target-ptr
d_store'45'indirect'45'suc'45'target'45'ptr_3934 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_store'45'indirect'45'suc'45'target'45'ptr_3934 v0 ~v1 v2 v3 v4 v5
                                                 ~v6
  = du_store'45'indirect'45'suc'45'target'45'ptr_3934 v0 v2 v3 v4 v5
du_store'45'indirect'45'suc'45'target'45'ptr_3934 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_store'45'indirect'45'suc'45'target'45'ptr_3934 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.du_site'45'store'45'ptr_3060
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_e'45'in1_34
         (coe du_st_3954 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_run'45'meets_1788 v0 erased v1 v2 v3 v4
            (coe du_env_3950 (coe v0) (coe v1) (coe v4)) erased))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.sc
d_sc_3948 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sc_3948 v0 ~v1 v2 ~v3 ~v4 v5 ~v6 = du_sc_3948 v0 v2 v5
du_sc_3948 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sc_3948 v0 v1 v2
  = coe du_run'45'shape'45'check_3822 (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.env
d_env_3950 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
d_env_3950 v0 ~v1 v2 ~v3 ~v4 v5 ~v6 = du_env_3950 v0 v2 v5
du_env_3950 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  Integer -> MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
du_env_3950 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_sc_3948 (coe v0) (coe v1) (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.chk
d_chk_3952 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chk_3952 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.st
d_st_3954 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
d_st_3954 v0 ~v1 v2 v3 v4 v5 ~v6 = du_st_3954 v0 v2 v3 v4 v5
du_st_3954 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
du_st_3954 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_state'45'at_980
      (coe du_env_3950 (coe v0) (coe v1) (coe v4))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_entry'45'expect_962
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
      (coe v2) (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v3))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.ok
d_ok_3956 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok_3956 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.store-nonptr-absurd
d_store'45'nonptr'45'absurd_3966 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_store'45'nonptr'45'absurd_3966 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.wits
d_wits_3984 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wits_3984 v0 ~v1 v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9
  = du_wits_3984 v0 v2 v3 v4 v6
du_wits_3984 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wits_3984 v0 v1 v2 v3 v4
  = coe
      du_store'45'indirect'45'target'45'ptr_3904 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.store-suc-nonptr-absurd
d_store'45'suc'45'nonptr'45'absurd_3994 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_store'45'suc'45'nonptr'45'absurd_3994 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.wits
d_wits_4012 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wits_4012 v0 ~v1 v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9
  = du_wits_4012 v0 v2 v3 v4 v6
du_wits_4012 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wits_4012 v0 v1 v2 v3 v4
  = coe
      du_store'45'indirect'45'suc'45'target'45'ptr_3934 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.branch-tag-scrutinee-wf
d_branch'45'tag'45'scrutinee'45'wf_4024 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_branch'45'tag'45'scrutinee'45'wf_4024 v0 ~v1 v2 v3 v4 ~v5 v6 ~v7
  = du_branch'45'tag'45'scrutinee'45'wf_4024 v0 v2 v3 v4 v6
du_branch'45'tag'45'scrutinee'45'wf_4024 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_branch'45'tag'45'scrutinee'45'wf_4024 v0 v1 v2 v3 v4
  = coe
      du_repack_4058
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.du_site'45'branch'45'tag_2432
         (coe
            MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_e'45'in1_34
            (coe du_st_4046 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               d_run'45'meets_1788 v0 erased v1 v2 v3 v4
               (coe du_env_4042 (coe v0) (coe v1) (coe v4)) erased)))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.sc
d_sc_4040 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sc_4040 v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 = du_sc_4040 v0 v2 v6
du_sc_4040 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sc_4040 v0 v1 v2
  = coe du_run'45'shape'45'check_3822 (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.env
d_env_4042 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
d_env_4042 v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 = du_env_4042 v0 v2 v6
du_env_4042 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  Integer -> MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
du_env_4042 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_sc_4040 (coe v0) (coe v1) (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.chk
d_chk_4044 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chk_4044 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.st
d_st_4046 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
d_st_4046 v0 ~v1 v2 v3 v4 ~v5 v6 ~v7 = du_st_4046 v0 v2 v3 v4 v6
du_st_4046 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24
du_st_4046 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_state'45'at_980
      (coe du_env_4042 (coe v0) (coe v1) (coe v4))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_entry'45'expect_962
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
      (coe v2) (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v3))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.ok
d_ok_4048 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok_4048 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.repack
d_repack_4058 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_repack_4058 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_repack_4058 v8
du_repack_4058 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_repack_4058 v0
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
d_store'45'indirect'45'inbounds_4074 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_store'45'indirect'45'inbounds_4074 v0 ~v1 ~v2 v3 v4 v5 v6 ~v7 ~v8
  = du_store'45'indirect'45'inbounds_4074 v0 v3 v4 v5 v6
du_store'45'indirect'45'inbounds_4074 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_store'45'indirect'45'inbounds_4074 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.du_ptr'45'bounds'45'cell_424
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v3)
      (coe
         du_run'45'ptr'45'bounds_3806 (coe v0) (coe v1) (coe v2) (coe v4))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.store-indirect-suc-inbounds
d_store'45'indirect'45'suc'45'inbounds_4094 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_store'45'indirect'45'suc'45'inbounds_4094 v0 ~v1 ~v2 v3 v4 ~v5 v6
                                            ~v7 ~v8
  = du_store'45'indirect'45'suc'45'inbounds_4094 v0 v3 v4 v6
du_store'45'indirect'45'suc'45'inbounds_4094 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_store'45'indirect'45'suc'45'inbounds_4094 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.du_ptr'45'bounds'45'suc_406
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
      (coe
         du_run'45'ptr'45'bounds_3806 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.load-indirect-target-wf
d_load'45'indirect'45'target'45'wf_4116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'target'45'wf_4116 v0 ~v1 v2 v3 v4 v5 ~v6
  = du_load'45'indirect'45'target'45'wf_4116 v0 v2 v3 v4 v5
du_load'45'indirect'45'target'45'wf_4116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'target'45'wf_4116 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Once.CCC.Codegen.ShapeTable.du_site'45'load'45'ptr_2284
              (coe
                 MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_e'45'in1_34
                 (coe
                    MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_state'45'at_980
                    (coe du_env_3860 (coe v0) (coe v1) (coe v4))
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_entry'45'expect_962
                       (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
                    (coe v2)
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v3))))
              (coe
                 MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                 (coe
                    MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3)))
                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    d_run'45'meets_1788 v0 erased v1 v2 v3 v4
                    (coe du_env_3860 (coe v0) (coe v1) (coe v4)) erased)) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                   (coe
                      (\ v8 v9 ->
                         coe
                           MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.du_ptr'45'bounds'45'cell_424
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v8)
                           (coe
                              du_run'45'ptr'45'bounds_3806 (coe v0) (coe v2) (coe v3)
                              (coe v4)))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.load-indirect-suc-target-wf
d_load'45'indirect'45'suc'45'target'45'wf_4154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'target'45'wf_4154 v0 ~v1 v2 v3 v4 v5
                                               ~v6
  = du_load'45'indirect'45'suc'45'target'45'wf_4154 v0 v2 v3 v4 v5
du_load'45'indirect'45'suc'45'target'45'wf_4154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'target'45'wf_4154 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Once.CCC.Codegen.ShapeTable.du_site'45'load'45'ptr_2284
              (coe
                 MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_e'45'in1_34
                 (coe
                    MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_state'45'at_980
                    (coe du_env_3890 (coe v0) (coe v1) (coe v4))
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_entry'45'expect_962
                       (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
                    (coe v2)
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v3))))
              (coe
                 MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                 (coe
                    MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v3)))
                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    d_run'45'meets_1788 v0 erased v1 v2 v3 v4
                    (coe du_env_3890 (coe v0) (coe v1) (coe v4)) erased)) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                   (coe
                      (\ v8 v9 ->
                         coe
                           MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.du_ptr'45'bounds'45'suc_406
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
                           (coe
                              du_run'45'ptr'45'bounds_3806 (coe v0) (coe v2) (coe v3)
                              (coe v4)))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.events-agree
d_events'45'agree_4200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_events'45'agree_4200 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du_events'45'agree_4200 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
du_events'45'agree_4200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_events'45'agree_4200 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v3 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             erased
      _ -> let v11 = subInt (coe v3) (coe (1 :: Integer)) in
           coe
             (coe
                du_go'45'h_4578 (coe v0) (coe v1) (coe v2) (coe v11) (coe v4)
                (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v7))))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.events-running
d_events'45'running_4218 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_events'45'running_4218 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                         ~v12
  = du_events'45'running_4218 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
du_events'45'running_4218 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_events'45'running_4218 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_go_4612 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_216 (coe v6)
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v7)))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.events-running-fetch
d_events'45'running'45'fetch_4238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_events'45'running'45'fetch_4238 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9
                                  v10 v11 v12 ~v13 v14
  = du_events'45'running'45'fetch_4238
      v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14
du_events'45'running'45'fetch_4238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_events'45'running'45'fetch_4238 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                   v10 v11 v12
  = case coe v9 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190
        -> coe
             du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v9)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'mov'45'to'45'output_688
                (coe v8) (coe v10))
             (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192
        -> coe
             du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v9)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'mov'45'to'45'input_712
                (coe v8) (coe v10))
             (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2194
        -> coe
             du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v9)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'mov'45'output'45'to'45'input2_760
                (coe v8) (coe v10))
             (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2196
        -> coe
             du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v9)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'mov'45'input2'45'to'45'output_736
                (coe v8) (coe v10))
             (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198
        -> coe
             du_load'45'indirect'45'step_4372 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
             (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200
        -> coe
             du_load'45'indirect'45'suc'45'step_4390 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
             (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202 v13
        -> coe
             du_load'45'from'45'slot'45'step_4410 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)
             (coe v10) (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204 v13
        -> coe
             du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v9)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'store'45'at'45'slot_2036
                (coe v7) (coe v8) (coe v13) (coe v10))
             (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206
        -> coe
             du_store'45'indirect'45'step_4468 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
             (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208
        -> coe
             du_store'45'indirect'45'suc'45'step_4486 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
             (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2210 v13
        -> coe
             du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v9)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'lea'45'slot_2910
                (coe v8) (coe v13) (coe v10))
             (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2212 v13
        -> coe
             du_restore'45'input'45'step_4430 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)
             (coe v10) (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2214 v13
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2216 v13
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2218 v13
        -> coe
             du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v9)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'reclaim'45'to_1104
                (coe v8) (coe v10))
             (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2220 v13
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2222
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2224
        -> coe
             d_events'45'running'45'call_1732 v0 erased v1 v2 v3 v4 v5 v6 v7 v8
             v10 v11 erased erased
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2226 v13
        -> coe
             du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v9)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'worklist'45'init_1036
                (coe v8) (coe v10))
             (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2228 v13
        -> coe
             du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v9)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'worklist'45'push_1782
                (coe v7) (coe v8) (coe v13) (coe v10))
             (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2230 v13
        -> coe
             du_worklist'45'pop'45'step_4450 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v13) (coe v10)
             (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2232 v13
        -> coe
             du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v9)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'worklist'45'check_1070
                (coe v8) (coe v10))
             (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2238 v13 v14 v15
        -> coe
             du_sigop'45'step_4510 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v13) (coe v14) (coe v15)
             (coe v10) (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2242 v13 v14 v15
        -> case coe v14 of
             MAlonzo.Code.Once.Type.C_fits'45'int_198
               -> coe
                    du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2242
                       (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v14) (coe v15))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'const_1584
                       (coe v8) (coe v15) (coe v10))
                    (coe v11)
             MAlonzo.Code.Once.Type.C_fits'45'float_200
               -> coe
                    du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2242
                       (coe MAlonzo.Code.Once.Type.C_Float_138) (coe v14) (coe v15))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'const'45'float_1634
                       (coe v8) (coe v15) (coe v10))
                    (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2244 v13
        -> coe
             du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v9)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'code'45'addr_1684
                (coe v8) (coe v13) (coe v10))
             (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2246
        -> coe
             du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v9)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'save'45'closure'45'reg_1732
                (coe v8) (coe v10))
             (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2248 v13
        -> coe
             du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v9)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'tag'45'lit_862
                (coe v8) (coe v13) (coe v10))
             (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2250 v13 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252 v13
        -> coe
             du_ccc'45'step'45'bs_4258 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_extend'45'view_2342
                (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v7)))
                (coe v13)
                (coe v1 v2 v6 v7 v8 v13 (d_inv'45'run_952 (coe v11)) v10 v12))
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v9)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'alloc'45'heap_2834
                (coe v7) (coe v8) (coe v13) (coe v10))
             (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2254 v13
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256 v13
        -> case coe v13 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_450
               -> coe
                    du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v9)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'scratch'45'one_888
                       (coe v8) (coe v10))
                    (coe v11)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_452
               -> coe
                    du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v9)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'scratch'45'zero_912
                       (coe v8) (coe v10))
                    (coe v11)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_454
               -> coe
                    du_scratch'45'dec'45'step_4336 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10) (coe v11)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_456
               -> coe
                    du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v9)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'scratch'45'load'45'count_960
                       (coe v8) (coe v10))
                    (coe v11)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_458
               -> coe
                    du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v9)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'count'45'zero_936
                       (coe v8) (coe v10))
                    (coe v11)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_460
               -> coe
                    du_count'45'inc'45'step_4354 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258 v13
        -> case coe v13 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176 v14
               -> coe
                    du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v9)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'label_986
                       (coe v8) (coe v10))
                    (coe v11)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178 v14
               -> coe
                    du_cjmp'45'step_4278 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7) (coe v8) (coe v14) (coe v10) (coe v11)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180 v14
               -> coe
                    du_branch'45'step_4298 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7) (coe v8) (coe v14) (coe v10) (coe v11)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182 v14
               -> coe
                    du_tag'45'branch'45'step_4318 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v14) (coe v10)
                    (coe v11)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2184 v14 v15
               -> coe
                    d_events'45'running'45'thunk_1754 v0 erased v1 v2 v3 v4 v5 v6 v7 v8
                    v14 v15 v10 v11 erased erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2186 v14
               -> coe
                    d_events'45'running'45'ret_1774 v0 erased v1 v2 v3 v4 v5 v6 v7 v8
                    v14 v10 v11 erased erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2260 v13
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.ccc-step-bs
d_ccc'45'step'45'bs_4258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ccc'45'step'45'bs_4258 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 ~v9 v10 v11
                         v12 ~v13 ~v14 ~v15 ~v16
  = du_ccc'45'step'45'bs_4258 v0 v2 v3 v4 v5 v6 v7 v8 v10 v11 v12
du_ccc'45'step'45'bs_4258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ccc'45'step'45'bs_4258 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatComposition.du_x86'45'len_156
            (coe v8))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               du_rec_5684 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10))))
      erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.cjmp-step
d_cjmp'45'step_4278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cjmp'45'step_4278 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13
                    ~v14
  = du_cjmp'45'step_4278 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_cjmp'45'step_4278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cjmp'45'step_4278 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_go'45'fl_5724 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v0)
         (coe v6) (coe v9))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.branch-step
d_branch'45'step_4298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_branch'45'step_4298 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                      ~v13 ~v14
  = du_branch'45'step_4298 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_branch'45'step_4298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_branch'45'step_4298 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_go'45'sv_5908 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v7)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.tag-branch-step
d_tag'45'branch'45'step_4318 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tag'45'branch'45'step_4318 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12 ~v13 ~v14
  = du_tag'45'branch'45'step_4318
      v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_tag'45'branch'45'step_4318 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_tag'45'branch'45'step_4318 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_go'45'loc_6110 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe du_wits_5956 (coe v0) (coe v1) (coe v6) (coe v7) (coe v11)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe du_wits_5956 (coe v0) (coe v1) (coe v6) (coe v7) (coe v11))))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.scratch-dec-step
d_scratch'45'dec'45'step_4336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_scratch'45'dec'45'step_4336 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                              v11 ~v12 ~v13
  = du_scratch'45'dec'45'step_4336 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
du_scratch'45'dec'45'step_4336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_scratch'45'dec'45'step_4336 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_go'45'sv_6192 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v7)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.count-inc-step
d_count'45'inc'45'step_4354 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_count'45'inc'45'step_4354 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            ~v12 ~v13
  = du_count'45'inc'45'step_4354 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
du_count'45'inc'45'step_4354 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_count'45'inc'45'step_4354 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_go'45'sv_6242 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v7)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.load-indirect-step
d_load'45'indirect'45'step_4372 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'step_4372 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                v11 ~v12 ~v13
  = du_load'45'indirect'45'step_4372
      v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
du_load'45'indirect'45'step_4372 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'step_4372 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_go'45'loc_6434 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe du_wits_6288 (coe v0) (coe v1) (coe v6) (coe v7) (coe v10)))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.load-indirect-suc-step
d_load'45'indirect'45'suc'45'step_4390 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'step_4390 v0 ~v1 v2 v3 v4 v5 v6 v7 v8
                                       v9 v10 v11 ~v12 ~v13
  = du_load'45'indirect'45'suc'45'step_4390
      v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
du_load'45'indirect'45'suc'45'step_4390 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'step_4390 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10
  = coe
      du_go'45'loc_6622 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe du_wits_6476 (coe v0) (coe v1) (coe v6) (coe v7) (coe v10)))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.load-from-slot-step
d_load'45'from'45'slot'45'step_4410 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'from'45'slot'45'step_4410 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9
                                    v10 v11 v12 ~v13 ~v14
  = du_load'45'from'45'slot'45'step_4410
      v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_load'45'from'45'slot'45'step_4410 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'from'45'slot'45'step_4410 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                     v10 v11
  = coe
      du_go'45'mem_6670 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
         (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v7))
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v7)))
         v9)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.restore-input-step
d_restore'45'input'45'step_4430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_restore'45'input'45'step_4430 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                v11 v12 ~v13 ~v14
  = du_restore'45'input'45'step_4430
      v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_restore'45'input'45'step_4430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_restore'45'input'45'step_4430 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                 v11
  = coe
      du_go'45'mem_6730 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
         (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v7))
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v7)))
         v9)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.worklist-pop-step
d_worklist'45'pop'45'step_4450 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_worklist'45'pop'45'step_4450 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                               v11 v12 ~v13 ~v14
  = du_worklist'45'pop'45'step_4450
      v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_worklist'45'pop'45'step_4450 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_worklist'45'pop'45'step_4450 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                v11
  = coe
      du_go'45'mem_6790 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
         (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v7))
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v7)))
         v9)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.store-indirect-step
d_store'45'indirect'45'step_4468 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_store'45'indirect'45'step_4468 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                 v11 ~v12 ~v13
  = du_store'45'indirect'45'step_4468
      v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
du_store'45'indirect'45'step_4468 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_store'45'indirect'45'step_4468 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_go'45'ptr_6848 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v7)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.store-indirect-suc-step
d_store'45'indirect'45'suc'45'step_4486 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_store'45'indirect'45'suc'45'step_4486 v0 ~v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11 ~v12 ~v13
  = du_store'45'indirect'45'suc'45'step_4486
      v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
du_store'45'indirect'45'suc'45'step_4486 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_store'45'indirect'45'suc'45'step_4486 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9 v10
  = coe
      du_go'45'ptr_6922 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v7)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.sigop-step
d_sigop'45'step_4510 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigop'45'step_4510 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                     v14 ~v15 ~v16
  = du_sigop'45'step_4510
      v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
du_sigop'45'step_4510 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigop'45'step_4510 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      du_go'45'eff_7002 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12) (coe v13)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_212 (coe v11))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim.sigop-external
d_sigop'45'external_4534 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigop'45'external_4534 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                         v13 v14 ~v15 ~v16
  = du_sigop'45'external_4534
      v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
du_sigop'45'external_4534 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigop'45'external_4534 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                          v13
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               du_rec_7054 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
               (coe v13))))
      erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-h
d_go'45'h_4578 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'h_4578 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13
  = du_go'45'h_4578 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_go'45'h_4578 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'h_4578 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = if coe v11
      then coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
             erased
      else coe
             du_events'45'running_4218 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go
d_go_4612 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_4612 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ~v12 v13 ~v14
  = du_go_4612 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v13
du_go_4612 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_4612 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v11 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
        -> coe
             du_events'45'running'45'fetch_4238 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v12)
             (coe v9) (coe v10) erased
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_events'45'running'45'end_1682
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.rec
d_rec_5684 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rec_5684 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 ~v9 v10 v11 v12 ~v13 ~v14
           ~v15 ~v16
  = du_rec_5684 v0 v2 v3 v4 v5 v6 v7 v8 v10 v11 v12
du_rec_5684 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rec_5684 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_events'45'agree_4200 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_570 v0
         v8 v6 v7)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v9))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v9)))
      (coe
         du_flat'45'inv'45'step_986 (coe v0) (coe v8) (coe v6) (coe v7)
         (coe v10))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.result
d_result_5686 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result_5686 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-fl
d_go'45'fl_5724 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'fl_5724 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13
                ~v14 v15 ~v16
  = du_go'45'fl_5724 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v15
du_go'45'fl_5724 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'fl_5724 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
        -> coe
             du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178 (coe v9)))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'jmp_1140
                (coe v6) (coe v8) (coe v13) (coe v10))
             (coe v11)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (2 :: Integer))
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_5734 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_5734 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.halt-s
d_halt'45's_5746 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_5746 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.fetch-x86
d_fetch'45'x86_5748 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_5748 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.s'
d_s''_5750 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_s''_5750 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15
  = du_s''_5750 v9
du_s''_5750 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_s''_5750 v0
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
d_step'45'eq_5752 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'eq_5752 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_5758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_5758 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.result
d_result_5764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result_5764 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-fl
d_go'45'fl_5800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'fl_5800 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13
                ~v14 v15 ~v16 v17 ~v18
  = du_go'45'fl_5800 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v15 v17
du_go'45'fl_5800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  Integer -> Maybe Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'fl_5800 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v12 of
      0 -> case coe v13 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
               -> coe
                    du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180
                          (coe v9)))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'branch'45'scratch'45'zero_2204
                       (coe v6) (coe v8) (coe (0 :: Integer)) (coe v14) (coe v10))
                    (coe v11)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (3 :: Integer))
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> case coe v13 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
               -> coe
                    du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180
                          (coe v9)))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'branch'45'scratch'45'zero_2204
                       (coe v6) (coe v8) (coe v12) (coe v14) (coe v10))
                    (coe v11)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180
                          (coe v9)))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'branch'45'nz_2962
                       (coe v8) (coe v10))
                    (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_5812 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_5812 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_5834 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_5834 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_5850 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_5850 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.dc
d_dc_5864 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_5864 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
          ~v13 ~v14 ~v15 ~v16
  = du_dc_5864 v11
du_dc_5864 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_5864 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.d_dataCorr_524
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.halt-s
d_halt'45's_5866 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_5866 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.rbx0
d_rbx0_5868 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rbx0_5868 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.fetch-cmp
d_fetch'45'cmp_5870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'cmp_5870 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.post-cmp
d_post'45'cmp_5872 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post'45'cmp_5872 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11
                   ~v12 ~v13 ~v14 ~v15 ~v16
  = du_post'45'cmp_5872 v9
du_post'45'cmp_5872 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post'45'cmp_5872 v0
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
d_step'45'cmp_5874 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'cmp_5874 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.fetch-je
d_fetch'45'je_5876 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'je_5876 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.post-je
d_post'45'je_5880 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post'45'je_5880 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16
  = du_post'45'je_5880 v9
du_post'45'je_5880 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post'45'je_5880 v0
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
d_step'45'je_5882 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'je_5882 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_5892 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_5892 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.result
d_result_5902 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result_5902 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-sv
d_go'45'sv_5908 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'sv_5908 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13
                ~v14 v15 ~v16
  = du_go'45'sv_5908 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v15
du_go'45'sv_5908 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'sv_5908 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v13
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v13
        -> coe
             du_go'45'fl_5800 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v13)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v0)
                (coe v6) (coe v9))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v13 v14 v15
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v13
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.wits
d_wits_5956 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wits_5956 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 v7 v8 ~v9 ~v10 ~v11 v12 ~v13
            ~v14
  = du_wits_5956 v0 v2 v7 v8 v12
du_wits_5956 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wits_5956 v0 v1 v2 v3 v4
  = coe
      du_branch'45'tag'45'scrutinee'45'wf_4024 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe d_inv'45'run_952 (coe v4))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-fl
d_go'45'fl_5966 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
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
d_go'45'fl_5966 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13
                ~v14 ~v15 v16 ~v17 ~v18 ~v19 v20 ~v21
  = du_go'45'fl_5966 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v16 v20
du_go'45'fl_5966 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  Integer -> Maybe Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'fl_5966 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v12 of
      0 -> case coe v13 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
               -> coe
                    du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182
                          (coe v9)))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'branch'45'tag'45'zero_2354
                       (coe v6) (coe v8) (coe (0 :: Integer)) (coe v14) (coe v10))
                    (coe v11)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (3 :: Integer))
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v14 = subInt (coe v12) (coe (1 :: Integer)) in
           coe
             (case coe v13 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                  -> coe
                       du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v5) (coe v6) (coe v7)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182
                             (coe v9)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'branch'45'tag'45'zero_2354
                          (coe v6) (coe v8) (coe v12) (coe v15) (coe v10))
                       (coe v11)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v5) (coe v6) (coe v7)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182
                             (coe v9)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'c'45'branch'45'tag'45'nz_2746
                          (coe v8) (coe v14) (coe v10))
                       (coe v11)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_5984 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_5984 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6016 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
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
d_hpost_6016 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6042 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6042 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.dc
d_dc_6066 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_6066 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_dc_6066 v11
du_dc_6066 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_6066 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.d_dataCorr_524
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.halt-s
d_halt'45's_6068 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_6068 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.fetch-cmp
d_fetch'45'cmp_6070 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'cmp_6070 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.post-cmp
d_post'45'cmp_6072 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post'45'cmp_6072 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11
                   ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_post'45'cmp_6072 v9
du_post'45'cmp_6072 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post'45'cmp_6072 v0
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
d_step'45'cmp_6074 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'cmp_6074 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.fetch-je
d_fetch'45'je_6076 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'je_6076 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.post-je
d_post'45'je_6080 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post'45'je_6080 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_post'45'je_6080 v9
du_post'45'je_6080 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post'45'je_6080 v0
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
d_step'45'je_6082 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'je_6082 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6088 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6088 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.result
d_result_6102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result_6102 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-loc
d_go'45'loc_6110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'loc_6110 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13
                 ~v14 v15 v16 ~v17 ~v18
  = du_go'45'loc_6110 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v15 v16
du_go'45'loc_6110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'loc_6110 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      seq (coe v12)
      (coe
         du_go'45'fl_5966 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
         (coe v13)
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v0)
            (coe v6) (coe v9)))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.dc
d_dc_6124 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_6124 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_dc_6124 v11
du_dc_6124 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_6124 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.d_dataCorr_524
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.addr-val
d_addr'45'val_6126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_addr'45'val_6126 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.rd-heap
d_rd'45'heap_6128 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rd'45'heap_6128 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.dc
d_dc_6144 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_6144 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_dc_6144 v11
du_dc_6144 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_6144 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.d_dataCorr_524
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.spc
d_spc_6146 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_spc_6146 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_spc_6146
du_spc_6146 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_spc_6146 = coe du_stack'45'ptr'45'current_3116
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.st-cf
d_st'45'cf_6148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_st'45'cf_6148 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.rdi-val
d_rdi'45'val_6152 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45'val_6152 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.rd-stack
d_rd'45'stack_6160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rd'45'stack_6160 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-sv
d_go'45'sv_6192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'sv_6192 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ~v12 ~v13
                v14 ~v15
  = du_go'45'sv_6192 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v14
du_go'45'sv_6192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'sv_6192 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v11 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v12
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v12
        -> coe
             du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_454))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'scratch'45'dec_2148
                (coe v8) (coe v9))
             (coe v10)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v12 v13 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v12
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-sv
d_go'45'sv_6242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'sv_6242 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ~v12 ~v13
                v14 ~v15
  = du_go'45'sv_6242 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v14
du_go'45'sv_6242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'sv_6242 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v11 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v12
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v12
        -> coe
             du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_460))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'count'45'inc_2096
                (coe v8) (coe v9))
             (coe v10)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v12 v13 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v12
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.wits
d_wits_6288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wits_6288 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 v7 v8 ~v9 ~v10 v11 ~v12 ~v13
  = du_wits_6288 v0 v2 v7 v8 v11
du_wits_6288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wits_6288 v0 v1 v2 v3 v4
  = coe
      du_load'45'indirect'45'target'45'wf_4116 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe d_inv'45'run_952 (coe v4))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-mem
d_go'45'mem_6296 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_6296 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ~v12 ~v13
                 ~v14 ~v15 ~v16 v17 ~v18
  = du_go'45'mem_6296 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v17
du_go'45'mem_6296 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_6296 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v11 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
        -> coe
             du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'indirect_1200
                (coe v0) (coe v2) (coe v8) (coe v12) (coe v9))
             (coe v10)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6312 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.stuckp
d_stuckp_6334 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stuckp_6334 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
              ~v12 ~v13 ~v14 ~v15 ~v16 ~v17
  = du_stuckp_6334
du_stuckp_6334 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stuckp_6334
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_load'45'indirect'45'heap'45'empty'45'stuck_2502
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.halt-s
d_halt'45's_6336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_6336 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6338 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6338 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.result
d_result_6348 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result_6348 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-stack
d_go'45'stack_6358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'stack_6358 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ~v12 ~v13
                   ~v14 ~v15 ~v16 v17 v18 ~v19
  = du_go'45'stack_6358 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v17 v18
du_go'45'stack_6358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'stack_6358 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      seq (coe v11)
      (case coe v12 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
           -> coe
                du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v6) (coe v7)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198)
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'indirect'45'stack_3040
                   (coe v0) (coe v2) (coe v8) (coe v13) (coe v9))
                (coe v10)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                erased
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6378 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
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
d_hpost_6378 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.stuckp
d_stuckp_6408 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stuckp_6408 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
              ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_stuckp_6408
du_stuckp_6408 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stuckp_6408
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_load'45'indirect'45'stack'45'empty'45'stuck_2556
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.halt-s
d_halt'45's_6410 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_6410 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6412 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.result
d_result_6426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result_6426 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-loc
d_go'45'loc_6434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'loc_6434 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ~v12 ~v13
                 v14 ~v15 ~v16
  = du_go'45'loc_6434 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v14
du_go'45'loc_6434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'loc_6434 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v11 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v12 v13
        -> coe
             du_go'45'stack_6358 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe du_stack'45'ptr'45'current_3116)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
                (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v7))
                (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v7)))
                v13)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v12
        -> coe
             du_go'45'mem_6296 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
                (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v7)) v12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.wits
d_wits_6476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wits_6476 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 v7 v8 ~v9 ~v10 v11 ~v12 ~v13
  = du_wits_6476 v0 v2 v7 v8 v11
du_wits_6476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wits_6476 v0 v1 v2 v3 v4
  = coe
      du_load'45'indirect'45'suc'45'target'45'wf_4154 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe d_inv'45'run_952 (coe v4))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-mem
d_go'45'mem_6484 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_6484 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ~v12 ~v13
                 ~v14 ~v15 ~v16 v17 ~v18
  = du_go'45'mem_6484 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v17
du_go'45'mem_6484 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_6484 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v11 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
        -> coe
             du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'indirect'45'suc_1264
                (coe v0) (coe v2) (coe v8) (coe v12) (coe v9))
             (coe v10)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6500 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6500 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.stuckp
d_stuckp_6522 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stuckp_6522 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
              ~v12 ~v13 ~v14 ~v15 ~v16 ~v17
  = du_stuckp_6522
du_stuckp_6522 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stuckp_6522
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_load'45'indirect'45'suc'45'heap'45'empty'45'stuck_2618
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.halt-s
d_halt'45's_6524 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_6524 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6526 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6526 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.result
d_result_6536 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result_6536 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-stack
d_go'45'stack_6546 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'stack_6546 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ~v12 ~v13
                   ~v14 ~v15 ~v16 v17 v18 ~v19
  = du_go'45'stack_6546 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v17 v18
du_go'45'stack_6546 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'stack_6546 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      seq (coe v11)
      (case coe v12 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
           -> coe
                du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v6) (coe v7)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200)
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'indirect'45'suc'45'stack_3120
                   (coe v0) (coe v2) (coe v8) (coe v13) (coe v9))
                (coe v10)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                erased
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6566 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
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
d_hpost_6566 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.stuckp
d_stuckp_6596 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stuckp_6596 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
              ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_stuckp_6596
du_stuckp_6596 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stuckp_6596
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_load'45'indirect'45'suc'45'stack'45'empty'45'stuck_2676
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.halt-s
d_halt'45's_6598 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_6598 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6600 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6600 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.result
d_result_6614 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result_6614 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-loc
d_go'45'loc_6622 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'loc_6622 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ~v12 ~v13
                 v14 ~v15 ~v16
  = du_go'45'loc_6622 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v14
du_go'45'loc_6622 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'loc_6622 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v11 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v12 v13
        -> coe
             du_go'45'stack_6546 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe du_stack'45'ptr'45'current'45'suc_3138)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
                (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v7))
                (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v7)))
                (addInt (coe (1 :: Integer)) (coe v13)))
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v12
        -> coe
             du_go'45'mem_6484 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
                (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v7))
                (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v12)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-mem
d_go'45'mem_6670 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_6670 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13
                 ~v14 v15 ~v16
  = du_go'45'mem_6670 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v15
du_go'45'mem_6670 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_6670 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
        -> coe
             du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202
                (coe v9))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'load'45'from'45'slot_1332
                (coe v0) (coe v2) (coe v8) (coe v13) (coe v10))
             (coe v11)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_slot'45'empty'45'stop_1558
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6680 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6680 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6692 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6692 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-mem
d_go'45'mem_6730 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_6730 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13
                 ~v14 v15 ~v16
  = du_go'45'mem_6730 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v15
du_go'45'mem_6730 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_6730 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
        -> coe
             du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2212
                (coe v9))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'restore'45'input_1392
                (coe v0) (coe v2) (coe v8) (coe v13) (coe v10))
             (coe v11)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_slot'45'empty'45'stop_1558
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6740 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6740 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6752 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6752 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-mem
d_go'45'mem_6790 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_6790 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13
                 ~v14 v15 ~v16
  = du_go'45'mem_6790 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v15
du_go'45'mem_6790 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_6790 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
        -> coe
             du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2230
                (coe v9))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'worklist'45'pop_1844
                (coe v0) (coe v2) (coe v8) (coe v13) (coe v10))
             (coe v11)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_slot'45'empty'45'stop_1558
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6800 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6812 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6812 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-ptr
d_go'45'ptr_6848 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'ptr_6848 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ~v12 ~v13
                 v14 ~v15
  = du_go'45'ptr_6848 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v14
du_go'45'ptr_6848 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'ptr_6848 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v11 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v12
        -> case coe v12 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v13 v14
               -> coe
                    du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7)
                    (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'store'45'indirect'45'stack_3204
                       (coe v0) (coe v2) (coe v7) (coe v8) (coe v14) (coe v9))
                    (coe v10)
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v13
               -> coe
                    du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7)
                    (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'store'45'indirect_1902
                       (coe v7) (coe v8) (coe v13) (coe v9)
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'sized_446
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.d_dataCorr_524
                             (coe v9))
                          v13
                          (coe
                             du_store'45'indirect'45'inbounds_4074 (coe v0) (coe v6) (coe v7)
                             (coe v13) (coe d_inv'45'run_952 (coe v10)))))
                    (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v12
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v12 v13 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v12
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6858 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6858 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6874 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6874 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-ptr
d_go'45'ptr_6922 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'ptr_6922 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ~v12 ~v13
                 v14 ~v15
  = du_go'45'ptr_6922 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v14
du_go'45'ptr_6922 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'ptr_6922 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v11 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v12
        -> case coe v12 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v13 v14
               -> coe
                    du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'store'45'indirect'45'suc'45'stack_3288
                       (coe v0) (coe v2) (coe v7) (coe v8) (coe v14) (coe v9))
                    (coe v10)
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v13
               -> coe
                    du_ccc'45'step'45'bs_4258 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.du_block'45'step'45'store'45'indirect'45'suc_1966
                       (coe v7) (coe v8) (coe v13) (coe v9)
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'sized_446
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.d_dataCorr_524
                             (coe v9))
                          (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v13))
                          (coe
                             du_store'45'indirect'45'suc'45'inbounds_4094 (coe v0) (coe v6)
                             (coe v7) (coe d_inv'45'run_952 (coe v10)))))
                    (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v12
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v12 v13 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v12
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6932 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6932 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.hpost
d_hpost_6948 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_6948 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.go-eff
d_go'45'eff_7002 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'eff_7002 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 ~v15 ~v16 v17 ~v18
  = du_go'45'eff_7002
      v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v17
du_go'45'eff_7002 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'eff_7002 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = case coe v14 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_124
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_rec_7014 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                      (coe v13))))
             erased
      MAlonzo.Code.Once.SigOp.Info.C_Emits_126
        -> coe
             du_sigop'45'external_4534 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13)
      MAlonzo.Code.Once.SigOp.Info.C_Halts_128
        -> coe
             du_sigop'45'external_4534 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.contract
d_contract_7010 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_contract_7010 v0 ~v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
                v14 ~v15 ~v16 ~v17
  = du_contract_7010 v0 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14
du_contract_7010 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_contract_7010 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      d_arith'45'sigop'45'contract_1808 v0 erased v1 v2 v3 v4 v5 v6 v7 v8
      v9 (d_inv'45'run_952 (coe v11)) erased erased v10 erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.pl
d_pl_7012 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pl_7012 v0 ~v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 ~v15
          ~v16 ~v17
  = du_pl_7012 v0 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14
du_pl_7012 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pl_7012 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         du_contract_7010 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.rec
d_rec_7014 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rec_7014 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 ~v15
           ~v16 ~v17
  = du_rec_7014 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
du_rec_7014 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rec_7014 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      du_events'45'agree_4200 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_242
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2238 (coe v9)
            (coe v10) (coe v11))
         (coe v7))
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v14 v15 v16 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
              (\ v17 v18 v19 ->
                 coe
                   MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z64.du_val'45'x86'45'64_160
                   v17 v18)
              v14 v16)
         (coe
            du_pl_7012 (coe v0) (coe v1) (coe v2) (coe v5) (coe v6) (coe v7)
            (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13))
         v8)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               du_contract_7010 (coe v0) (coe v1) (coe v2) (coe v5) (coe v6)
               (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
               (coe v13))))
      (coe
         du_flat'45'inv'45'step_986 (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2238 (coe v9)
            (coe v10) (coe v11))
         (coe v6) (coe v7) (coe v13))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._._.goal
d_goal_7016 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_goal_7016 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.contract
d_contract_7052 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_contract_7052 v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                ~v15 ~v16
  = du_contract_7052 v0 v2 v3 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
du_contract_7052 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_contract_7052 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      d_external'45'sigop'45'contract_1828 v0 erased v1 v2 v3 v4 v5 v6 v7
      v8 v9 v10 (d_inv'45'run_952 (coe v12)) erased erased v11 erased
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.rec
d_rec_7054 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rec_7054 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 ~v15
           ~v16
  = du_rec_7054 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
du_rec_7054 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rec_7054 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      du_events'45'agree_4200 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_242
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2238 (coe v9)
            (coe v10) (coe v11))
         (coe v7))
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.RunTrace.d_ret'45'past_14
         (coe v8))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               du_contract_7052 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
               (coe v13))))
      (coe
         du_flat'45'inv'45'step_986 (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2238 (coe v9)
            (coe v10) (coe v11))
         (coe v6) (coe v7) (coe v13))
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim._.goal
d_goal_7056 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_204 ->
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
  T_FlatInv_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_goal_7056 = erased
