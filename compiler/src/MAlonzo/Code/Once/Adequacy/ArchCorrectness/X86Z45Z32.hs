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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32 where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ConcFlatSim
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.RegRoles
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds
import qualified MAlonzo.Code.Once.Adequacy.CPU
import qualified MAlonzo.Code.Once.Adequacy.CPU.Interface
import qualified MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z32
import qualified MAlonzo.Code.Once.Adequacy.Compile
import qualified MAlonzo.Code.Once.Adequacy.FlatEvents
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF
import qualified MAlonzo.Code.Once.CCC.Machine.FlatStoreWF
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.AbstractToX86Z45Z32
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.FrameInstantiation
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Memory.StackSlots
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg
import qualified MAlonzo.Code.Once.Word

-- Once.Adequacy.ArchCorrectness.X86-32._.IRObsCorrectFlatness.ir-obs-correct
d_ir'45'obs'45'correct_82 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1480 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1432
d_ir'45'obs'45'correct_82 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_ir'45'obs'45'correct_82 v0
du_ir'45'obs'45'correct_82 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1480 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1432
du_ir'45'obs'45'correct_82 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_3546
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.ir-stack-budget
d_ir'45'stack'45'budget_192 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget_192 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_ir'45'stack'45'budget_192 v0
du_ir'45'stack'45'budget_192 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
du_ir'45'stack'45'budget_192 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_742
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.ir-to-trace
d_ir'45'to'45'trace_194 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_ir'45'to'45'trace_194 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_ir'45'to'45'trace_194 v0
du_ir'45'to'45'trace_194 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_ir'45'to'45'trace_194 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_724
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.ir-obs-correct
d_ir'45'obs'45'correct_210 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1480 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1432
d_ir'45'obs'45'correct_210 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_ir'45'obs'45'correct_210 v0 v1
du_ir'45'obs'45'correct_210 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1480 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1432
du_ir'45'obs'45'correct_210 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_3546
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.FrameInstantiation.d_x86'45'32'45'frame'45'semantics_308)
      (coe v1)
-- Once.Adequacy.ArchCorrectness.X86-32.stack-top-in-stack
d_stack'45'top'45'in'45'stack_240
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-32.stack-top-in-stack"
-- Once.Adequacy.ArchCorrectness.X86-32.entry-frame-x86-32
d_entry'45'frame'45'x86'45'32_242 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14
d_entry'45'frame'45'x86'45'32_242 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Memory.StackSlots.C_stack'45'addr_24
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_stack'45'top_322)
      (coe d_stack'45'top'45'in'45'stack_240 v0 v1 v2 v3 v4 v5 v6 v7 v8)
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.AsmTraceCorrect
d_AsmTraceCorrect_246 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  (Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
   Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  ()
d_AsmTraceCorrect_246 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.asm-sem
d_asm'45'sem_248 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_asm'45'sem_248 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_asm'45'sem_248
du_asm'45'sem_248 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_asm'45'sem_248
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_asm'45'sem_990
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10))
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-alloc
d_entry'45'alloc_250 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_entry'45'alloc_250 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'alloc_998
      (coe
         d_entry'45'frame'45'x86'45'32_242 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8))
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-bf
d_entry'45'bf_252 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_entry'45'bf_252 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_entry'45'bf_252
du_entry'45'bf_252 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_entry'45'bf_252 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'bf_1022
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-loc
d_entry'45'loc_254 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_entry'45'loc_254 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_entry'45'loc_254
du_entry'45'loc_254 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_entry'45'loc_254
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'loc_1004
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-nh
d_entry'45'nh_256 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'nh_256 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-ns
d_entry'45'ns_258 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_entry'45'ns_258 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_entry'45'ns_258
du_entry'45'ns_258 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_entry'45'ns_258 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'ns_1018
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-regs
d_entry'45'regs_260 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
d_entry'45'regs_260 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_entry'45'regs_260
du_entry'45'regs_260 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
du_entry'45'regs_260
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'regs_1006
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-s
d_entry'45's_262 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_entry'45's_262 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_entry'45's_262
du_entry'45's_262 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_entry'45's_262
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45's_1008
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-size
d_entry'45'size_264 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_entry'45'size_264 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.d_entry'45'size_996
      v0 (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.FrameInstantiation.d_x86'45'32'45'frame'45'semantics_308
      erased
      (d_entry'45'frame'45'x86'45'32_242
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8))
      (MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10))
      v1
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-span
d_entry'45'span_266 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'span_266 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-vr
d_entry'45'vr_268 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1480 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1432) ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1344
d_entry'45'vr_268 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'vr_1056
      (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.FrameInstantiation.d_x86'45'32'45'frame'45'semantics_308)
      (coe
         d_entry'45'frame'45'x86'45'32_242 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8))
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10))
      (coe v1)
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-witness
d_entry'45'witness_270 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1480 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1432) ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1432
d_entry'45'witness_270 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'witness_1042
      (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.FrameInstantiation.d_x86'45'32'45'frame'45'semantics_308)
      (coe
         d_entry'45'frame'45'x86'45'32_242 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8))
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10))
      (coe v1)
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.flat-from-obs
d_flat'45'from'45'obs_272 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1480 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1432) ->
  (MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Adequacy.Compile.T_ArchCorrect_48
d_flat'45'from'45'obs_272 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_flat'45'from'45'obs_1120
      (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.FrameInstantiation.d_x86'45'32'45'frame'45'semantics_308)
      (coe
         d_entry'45'frame'45'x86'45'32_242 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8))
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10))
      (coe v1) v9
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.flat-trace-of
d_flat'45'trace'45'of_274 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1480 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1432) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_flat'45'trace'45'of_274 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_flat'45'trace'45'of_1068
      (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.FrameInstantiation.d_x86'45'32'45'frame'45'semantics_308)
      (coe
         d_entry'45'frame'45'x86'45'32_242 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8))
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10))
      (coe v1)
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.ir-flat-correct-of
d_ir'45'flat'45'correct'45'of_276 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1480 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1432) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'flat'45'correct'45'of_276 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.entry-frame-base
d_entry'45'frame'45'base_278 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'frame'45'base_278 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.as32
d_as32_280 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10
d_as32_280 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 = du_as32_280
du_as32_280 ::
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10
du_as32_280
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
      (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10)
-- Once.Adequacy.ArchCorrectness.X86-32.conc-trace
d_conc'45'trace_282 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_conc'45'trace_282 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_conc'45'trace_282 v0 v9
du_conc'45'trace_282 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_conc'45'trace_282 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Once.Adequacy.CPU.Interface.d_run'45'trace_34
             (coe du_as32_280)
             (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.AbstractToX86Z45Z32.d_compile'45'trace'45'cnt_222
                   (coe v0) (coe (0 :: Integer))
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_724
                      (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                      (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2))))
             (MAlonzo.Code.Once.Adequacy.CPU.Interface.d_initialState_30
                (coe du_as32_280))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe (\ v2 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-32.x86-32-loader-faithful
d_x86'45'32'45'loader'45'faithful_292
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-32.x86-32-loader-faithful"
-- Once.Adequacy.ArchCorrectness.X86-32._.flat-events
d_flat'45'events_300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_flat'45'events_300 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_flat'45'events_300
du_flat'45'events_300 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_flat'45'events_300
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_434
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.FrameInstantiation.d_x86'45'32'45'frame'45'semantics_308)
-- Once.Adequacy.ArchCorrectness.X86-32._.CompiledCorr
d_CompiledCorr_304 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
-- Once.Adequacy.ArchCorrectness.X86-32._.EntryLike
d_EntryLike_308 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_EntryLike_308 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._.FlatInv
d_FlatInv_310 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
-- Once.Adequacy.ArchCorrectness.X86-32._.HeapView
d_HeapView_314 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.Adequacy.ArchCorrectness.X86-32._.Reachable
d_Reachable_318 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
-- Once.Adequacy.ArchCorrectness.X86-32._.CompiledCorr.code-eq
d_code'45'eq_338 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'eq_338 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._.CompiledCorr.dataCorr
d_dataCorr_340 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1056
d_dataCorr_340 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_678
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.CompiledCorr.pc-off
d_pc'45'off_342 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pc'45'off_342 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._.CompiledCorr.ret-eq
d_ret'45'eq_344 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
  AgdaAny
d_ret'45'eq_344 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_ret'45'eq_682
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.FlatInv.inv-closure
d_inv'45'closure_348 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1030 ->
  AgdaAny
d_inv'45'closure_348 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'closure_1054
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.FlatInv.inv-env
d_inv'45'env_350 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1030 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv'45'env_350 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._.FlatInv.inv-ev
d_inv'45'ev_352 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1030 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv'45'ev_352 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._.FlatInv.inv-regtag
d_inv'45'regtag_354 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1030 ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_470
d_inv'45'regtag_354 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'regtag_1056
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.FlatInv.inv-run
d_inv'45'run_356 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1030 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362
d_inv'45'run_356 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1062
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.FlatInv.inv-wf
d_inv'45'wf_358 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1030 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_662
d_inv'45'wf_358 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'wf_1052
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.HeapView.HDom
d_HDom_362 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> ()
d_HDom_362 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._.HeapView.caddr
d_caddr_364 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_caddr_364 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_caddr_470
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.HeapView.dom-below
d_dom'45'below_366 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_366 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'below_484
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.HeapView.front-lo
d_front'45'lo_368 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo_368 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_front'45'lo_488
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.HeapView.haddr
d_haddr_370 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_haddr_370 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_haddr_464
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.HeapView.haddr-inj
d_haddr'45'inj_372 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_372 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._.HeapView.haddr-suc
d_haddr'45'suc_374 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_374 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._.HeapView.hfront
d_hfront_376 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
  Integer
d_hfront_376 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_468
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.HeapView.lo
d_lo_378 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
  Integer
d_lo_378 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_486
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.FlatWF
d_FlatWF_388 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_FlatWF_388 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._.sv-below
d_sv'45'below_390 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_sv'45'below_390 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._.FlatRegTag
d_FlatRegTag_394 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_FlatRegTag_394 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.code-map
d_code'45'map_396 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_code'45'map_396 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_code'45'map_396 v9 v10
du_code'45'map_396 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
du_code'45'map_396 v0 v1
  = coe
      du_pick_406
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_find'45'label_400
         (coe v0) (coe MAlonzo.Code.Once.CCC.Label.C_thunk_28 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-32._.pick
d_pick_406 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer -> Integer
d_pick_406 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_pick_406 v11
du_pick_406 :: Maybe Integer -> Integer
du_pick_406 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-32.entry-view
d_entry'45'view_410 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436
d_entry'45'view_410 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_entry'45'view_410 v9
du_entry'45'view_410 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436
du_entry'45'view_410 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.C_mkHV_490
      (\ v1 ->
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.AbstractToX86Z45Z32.d_slot'45'to'45'disp_164
           (coe
              MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50 (coe v1)))
      (0 :: Integer) (coe du_code'45'map_396 (coe v0)) erased
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_stack'45'top_322
      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
-- Once.Adequacy.ArchCorrectness.X86-32._.suc-law
d_suc'45'law_420 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45'law_420 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.main-heap-moded
d_main'45'heap'45'moded_432
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-32.main-heap-moded"
-- Once.Adequacy.ArchCorrectness.X86-32.entry-corr
d_entry'45'corr_436 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656
d_entry'45'corr_436 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_entry'45'corr_436
du_entry'45'corr_436 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656
du_entry'45'corr_436
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.C_constructor_690
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.C_constructor_1148
         erased erased erased
         (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_stack'45'top_322))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_stack'45'top_322))
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.ArchCorrectness.X86-32._.cong-pick
d_cong'45'pick_448 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong'45'pick_448 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.entry-wf
d_entry'45'wf_482 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_662
d_entry'45'wf_482 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_entry'45'wf_482
du_entry'45'wf_482 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_662
du_entry'45'wf_482
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.C_constructor_704
      (coe du_reg'45'below_492)
      (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.ArchCorrectness.X86-32._.reg-below
d_reg'45'below_492 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
d_reg'45'below_492 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_reg'45'below_492 v10
du_reg'45'below_492 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
du_reg'45'below_492 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.ArchCorrectness.X86-32.entry-regtag
d_entry'45'regtag_506 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_470
d_entry'45'regtag_506 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_entry'45'regtag_506
du_entry'45'regtag_506 ::
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_470
du_entry'45'regtag_506
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.C_mkRegTagWF_482
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         erased)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         erased)
-- Once.Adequacy.ArchCorrectness.X86-32.entry-like
d_entry'45'like_512 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_entry'45'like_512 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_entry'45'like_512
du_entry'45'like_512 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_entry'45'like_512
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))))))))
-- Once.Adequacy.ArchCorrectness.X86-32._.no-ptr
d_no'45'ptr_524 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'ptr_524 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.entry-inv
d_entry'45'inv_544 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1030
d_entry'45'inv_544 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.C_mkFlatInv_1064
      (coe du_entry'45'wf_482)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe du_entry'45'regtag_506)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_mkRunAt_384
         v9 (coe d_main'45'heap'45'moded_432 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9)
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_reach'45'start_344
            (coe du_entry'45'like_512)))
-- Once.Adequacy.ArchCorrectness.X86-32.Nof
d_Nof_548 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer -> Integer
d_Nof_548 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10
  = du_Nof_548 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
du_Nof_548 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
du_Nof_548 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_steps_1388
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_value'45'realized_1462
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'witness_1042
            (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10)
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z32.FrameInstantiation.d_x86'45'32'45'frame'45'semantics_308)
            (coe
               d_entry'45'frame'45'x86'45'32_242 (coe v0) (coe v1) (coe v2)
               (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8))
            (coe
               MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
               (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10))
            (coe v1) (coe v9)
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_3546
               (coe v0)
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.FrameInstantiation.d_x86'45'32'45'frame'45'semantics_308)
               (coe v1) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v9))))
-- Once.Adequacy.ArchCorrectness.X86-32.conc-fuel
d_conc'45'fuel_560
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-32.conc-fuel"
-- Once.Adequacy.ArchCorrectness.X86-32.conc-flat-sim-just
d_conc'45'flat'45'sim'45'just_566 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_conc'45'flat'45'sim'45'just_566 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._.agree
d_agree_576 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_agree_576 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10
  = du_agree_576 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
du_agree_576 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_agree_576 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.du_events'45'agree_1436
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.FrameInstantiation.d_x86'45'32'45'frame'45'semantics_308)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_68)
      (coe
         MAlonzo.Code.Data.Nat.Base.C_constructor_120
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.RegRoles.d_x86'45'32'45'roles_12)
      (coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (32 :: Integer)))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ConcFlatSim.du_x86'45'32'45'emitter_1898)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ConcFlatSim.du_x86'45'32'45'machine_1924)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ConcFlatSim.du_x86'45'32'45'traceloop_1926)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ConcFlatSim.du_x86'45'32'45'supply_3418
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.FrameInstantiation.d_x86'45'32'45'frame'45'semantics_308)
         (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.d_ret'45'no'45'wrap_268
            (coe v7))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.d_count'45'no'45'wrap_278
            (coe v7))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.d_tag'45'fits_328
            (coe v8))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.d_lit'45'fits_340
            (coe v8))
         (\ v10 v11 v12 v13 v14 v15 v16 v17 ->
            coe
              MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.du_float'45'fits_354
              v14)
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.d_lo'45'fits_288
            (coe v7)))
      (coe
         du_entry'45'view_410
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.AbstractToX86Z45Z32.d_compile'45'trace_290
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_724
               (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v9))))
      (coe
         du_Nof_548 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8) (coe v9))
      (coe MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z32.d_ev'45'x86'45'32_10)
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z32.d_arith'45'env'45'x86'45'32_12
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z32.AbstractToX86Z45Z32.d_compile'45'trace_290
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_724
               (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v9))))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_724
         (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v9))
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45's_1008)
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'alloc_998
            (coe
               d_entry'45'frame'45'x86'45'32_242 (coe v0) (coe v1) (coe v2)
               (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_742
               (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v9)))
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72
            (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.Interface.d_initialState_30
         (coe du_as32_280))
      (coe du_entry'45'corr_436)
      (coe
         d_entry'45'inv_544 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7) (coe v8) (coe v9))
-- Once.Adequacy.ArchCorrectness.X86-32.x86-32-conc-flat-sim
d_x86'45'32'45'conc'45'flat'45'sim_586 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x86'45'32'45'conc'45'flat'45'sim_586 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.asm-trace-correct-x86-32
d_asm'45'trace'45'correct'45'x86'45'32_594 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_asm'45'trace'45'correct'45'x86'45'32_594 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.x86-32-correct
d_x86'45'32'45'correct_606 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.Adequacy.Compile.T_ArchCorrect_48
d_x86'45'32'45'correct_606 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_flat'45'from'45'obs_1120
      (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.FrameInstantiation.d_x86'45'32'45'frame'45'semantics_308)
      (coe
         d_entry'45'frame'45'x86'45'32_242 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8))
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10))
      (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_3546
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.FrameInstantiation.d_x86'45'32'45'frame'45'semantics_308)
         (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-32._.RunAt
d_RunAt_7425 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
