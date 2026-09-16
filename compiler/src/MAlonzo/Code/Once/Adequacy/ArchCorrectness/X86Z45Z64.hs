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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64 where

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
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RegRoles
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds
import qualified MAlonzo.Code.Once.Adequacy.CPU
import qualified MAlonzo.Code.Once.Adequacy.CPU.Interface
import qualified MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z64
import qualified MAlonzo.Code.Once.Adequacy.Compile
import qualified MAlonzo.Code.Once.Adequacy.FlatEvents
import qualified MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface
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
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Behavior
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Memory.StackSlots
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg
import qualified MAlonzo.Code.Once.Word

-- Once.Adequacy.ArchCorrectness.X86-64._.IRObsCorrectFlatness.ir-obs-correct
d_ir'45'obs'45'correct_388 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3918 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3706 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3660
d_ir'45'obs'45'correct_388 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_ir'45'obs'45'correct_388 v0
du_ir'45'obs'45'correct_388 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3918 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3706 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3660
du_ir'45'obs'45'correct_388 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_5544
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.ir-stack-budget
d_ir'45'stack'45'budget_1446 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget_1446 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_ir'45'stack'45'budget_1446 v0
du_ir'45'stack'45'budget_1446 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
du_ir'45'stack'45'budget_1446 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_830
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.ir-to-trace
d_ir'45'to'45'trace_1448 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_ir'45'to'45'trace_1448 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_ir'45'to'45'trace_1448 v0
du_ir'45'to'45'trace_1448 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_ir'45'to'45'trace_1448 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_812
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.ir-obs-correct
d_ir'45'obs'45'correct_1464 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3918 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3706 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3660
d_ir'45'obs'45'correct_1464 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_ir'45'obs'45'correct_1464 v0
du_ir'45'obs'45'correct_1464 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3918 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3706 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3660
du_ir'45'obs'45'correct_1464 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_5544
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
-- Once.Adequacy.ArchCorrectness.X86-64.stack-top-in-stack
d_stack'45'top'45'in'45'stack_1502
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.stack-top-in-stack"
-- Once.Adequacy.ArchCorrectness.X86-64.entry-frame-x86-64
d_entry'45'frame'45'x86'45'64_1504 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14
d_entry'45'frame'45'x86'45'64_1504 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Memory.StackSlots.C_stack'45'addr_24
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_stack'45'top_400)
      (coe d_stack'45'top'45'in'45'stack_1502 v0 v1 v2 v3 v4 v5 v6 v7)
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.AsmTraceCorrect
d_AsmTraceCorrect_1508 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  (Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6) ->
  ()
d_AsmTraceCorrect_1508 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.asm-sem
d_asm'45'sem_1510 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_asm'45'sem_1510 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_asm'45'sem_1510
du_asm'45'sem_1510 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
du_asm'45'sem_1510
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_asm'45'sem_2284
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.block-runs
d_block'45'runs_1512 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3918
d_block'45'runs_1512 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.d_block'45'runs_2332
      v0 (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308
      erased
      (d_entry'45'frame'45'x86'45'64_1504
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7))
      (MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-alloc
d_entry'45'alloc_1514 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_entry'45'alloc_1514 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'alloc_2288
      (coe
         d_entry'45'frame'45'x86'45'64_1504 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-bf
d_entry'45'bf_1516 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_entry'45'bf_1516 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_entry'45'bf_1516
du_entry'45'bf_1516 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_entry'45'bf_1516 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'bf_2312
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-blocks
d_entry'45'blocks_1518 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_entry'45'blocks_1518 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.d_entry'45'blocks_2336
      v0 (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308
      erased
      (d_entry'45'frame'45'x86'45'64_1504
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7))
      (MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-loc
d_entry'45'loc_1520 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_entry'45'loc_1520 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_entry'45'loc_1520
du_entry'45'loc_1520 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_entry'45'loc_1520
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'loc_2294
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-nh
d_entry'45'nh_1522 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'nh_1522 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-ns
d_entry'45'ns_1524 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_entry'45'ns_1524 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_entry'45'ns_1524
du_entry'45'ns_1524 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_entry'45'ns_1524 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'ns_2308
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-regs
d_entry'45'regs_1526 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
d_entry'45'regs_1526 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_entry'45'regs_1526
du_entry'45'regs_1526 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
du_entry'45'regs_1526
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'regs_2296
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-s
d_entry'45's_1528 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_entry'45's_1528 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_entry'45's_1528
du_entry'45's_1528 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_entry'45's_1528
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45's_2298
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-span
d_entry'45'span_1530 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'span_1530 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-vr
d_entry'45'vr_1532 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3918 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3706 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3660) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488
d_entry'45'vr_1532 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'vr_2360
      (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
      (coe
         d_entry'45'frame'45'x86'45'64_1504 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-witness
d_entry'45'witness_1534 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3918 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3706 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3660) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3660
d_entry'45'witness_1534 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'witness_2342
      (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
      (coe
         d_entry'45'frame'45'x86'45'64_1504 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.flat-from-obs
d_flat'45'from'45'obs_1536 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3918 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3706 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3660) ->
  (MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Adequacy.Compile.T_ArchCorrect_48
d_flat'45'from'45'obs_1536 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_flat'45'from'45'obs_2474
      (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
      (coe
         d_entry'45'frame'45'x86'45'64_1504 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
      v8
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.flat-trace-fam
d_flat'45'trace'45'fam_1538 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3918 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3706 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3660) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_flat'45'trace'45'fam_1538 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_flat'45'trace'45'fam_2374
      (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
      (coe
         d_entry'45'frame'45'x86'45'64_1504 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.flat-trace-of
d_flat'45'trace'45'of_1540 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3918 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3706 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3660) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_flat'45'trace'45'of_1540 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_flat'45'trace'45'of_2424
      (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
      (coe
         d_entry'45'frame'45'x86'45'64_1504 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.ir-flat-correct-fam
d_ir'45'flat'45'correct'45'fam_1542 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3918 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3706 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3660) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'flat'45'correct'45'fam_1542 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.ir-flat-correct-of
d_ir'45'flat'45'correct'45'of_1544 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3918 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3706 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3660) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'flat'45'correct'45'of_1544 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.rewrite-preserves-of
d_rewrite'45'preserves'45'of_1546 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3918 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3706 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3660) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rewrite'45'preserves'45'of_1546 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.entry-frame-base
d_entry'45'frame'45'base_1548 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'frame'45'base_1548 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.as64
d_as64_1550 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10
d_as64_1550 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 = du_as64_1550
du_as64_1550 ::
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10
du_as64_1550
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
      (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
-- Once.Adequacy.ArchCorrectness.X86-64.conc-trace
d_conc'45'trace_1552 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_conc'45'trace_1552 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_conc'45'trace_1552 v0 v8
du_conc'45'trace_1552 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
du_conc'45'trace_1552 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Once.Adequacy.CPU.Interface.d_run'45'trace_34
             (coe du_as64_1550)
             (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_compile'45'trace'45'cnt_68
                   (coe v0) (coe (0 :: Integer))
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_812
                      (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                      (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2))))
             (MAlonzo.Code.Once.Adequacy.CPU.Interface.d_initialState_30
                (coe du_as64_1550))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Denotation.Behavior.d_silent_42
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.x86-64-loader-faithful
d_x86'45'64'45'loader'45'faithful_1562
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.x86-64-loader-faithful"
-- Once.Adequacy.ArchCorrectness.X86-64._.flat-events
d_flat'45'events_1570 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_flat'45'events_1570 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_flat'45'events_1570
du_flat'45'events_1570 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_flat'45'events_1570
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_438
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
-- Once.Adequacy.ArchCorrectness.X86-64._.CompiledCorr
d_CompiledCorr_1574 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
-- Once.Adequacy.ArchCorrectness.X86-64._.EntryLike
d_EntryLike_1578 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_EntryLike_1578 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatInv
d_FlatInv_1580 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView
d_HeapView_1584 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.Adequacy.ArchCorrectness.X86-64._.Reachable
d_Reachable_1588 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
-- Once.Adequacy.ArchCorrectness.X86-64._.CompiledCorr.code-eq
d_code'45'eq_1608 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'eq_1608 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.CompiledCorr.dataCorr
d_dataCorr_1610 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1056
d_dataCorr_1610 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_678
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.CompiledCorr.pc-off
d_pc'45'off_1612 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pc'45'off_1612 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.CompiledCorr.ret-eq
d_ret'45'eq_1614 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
  AgdaAny
d_ret'45'eq_1614 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_ret'45'eq_682
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatInv.inv-closure
d_inv'45'closure_1618 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1036 ->
  AgdaAny
d_inv'45'closure_1618 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'closure_1060
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatInv.inv-env
d_inv'45'env_1620 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1036 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv'45'env_1620 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatInv.inv-ev
d_inv'45'ev_1622 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1036 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv'45'ev_1622 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatInv.inv-regtag
d_inv'45'regtag_1624 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1036 ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_472
d_inv'45'regtag_1624 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'regtag_1062
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatInv.inv-run
d_inv'45'run_1626 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1036 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362
d_inv'45'run_1626 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1068
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatInv.inv-wf
d_inv'45'wf_1628 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1036 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_664
d_inv'45'wf_1628 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'wf_1058
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.HDom
d_HDom_1632 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> ()
d_HDom_1632 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.caddr
d_caddr_1634 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_caddr_1634 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_caddr_470
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.dom-below
d_dom'45'below_1636 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_1636 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'below_484
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.front-lo
d_front'45'lo_1638 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo_1638 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_front'45'lo_488
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.haddr
d_haddr_1640 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_haddr_1640 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_haddr_464
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.haddr-inj
d_haddr'45'inj_1642 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_1642 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.haddr-suc
d_haddr'45'suc_1644 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_1644 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.hfront
d_hfront_1646 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
  Integer
d_hfront_1646 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_468
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.lo
d_lo_1648 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
  Integer
d_lo_1648 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_486
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatWF
d_FlatWF_1658 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_FlatWF_1658 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.sv-below
d_sv'45'below_1660 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_sv'45'below_1660 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatRegTag
d_FlatRegTag_1664 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_FlatRegTag_1664 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.code-map
d_code'45'map_1666 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_code'45'map_1666 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_code'45'map_1666 v8 v9
du_code'45'map_1666 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
du_code'45'map_1666 v0 v1
  = coe
      du_pick_1676
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_find'45'label_484
         (coe v0) (coe MAlonzo.Code.Once.CCC.Label.C_thunk_28 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64._.pick
d_pick_1676 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer -> Integer
d_pick_1676 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_pick_1676 v10
du_pick_1676 :: Maybe Integer -> Integer
du_pick_1676 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.entry-view
d_entry'45'view_1680 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436
d_entry'45'view_1680 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_entry'45'view_1680 v8
du_entry'45'view_1680 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436
du_entry'45'view_1680 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.C_mkHV_490
      (\ v1 ->
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_slot'45'to'45'disp_10
           (coe
              MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50 (coe v1)))
      (0 :: Integer) (coe du_code'45'map_1666 (coe v0)) erased
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_stack'45'top_400
      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
-- Once.Adequacy.ArchCorrectness.X86-64._.suc-law
d_suc'45'law_1690 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45'law_1690 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.main-heap-moded
d_main'45'heap'45'moded_1702
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.main-heap-moded"
-- Once.Adequacy.ArchCorrectness.X86-64.entry-corr
d_entry'45'corr_1706 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656
d_entry'45'corr_1706 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_entry'45'corr_1706
du_entry'45'corr_1706 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656
du_entry'45'corr_1706
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.C_constructor_690
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.C_constructor_1148
         erased erased erased
         (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_stack'45'top_400))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_stack'45'top_400))
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.ArchCorrectness.X86-64._.cong-pick
d_cong'45'pick_1718 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong'45'pick_1718 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.entry-wf
d_entry'45'wf_1752 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_664
d_entry'45'wf_1752 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_entry'45'wf_1752
du_entry'45'wf_1752 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_664
du_entry'45'wf_1752
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.C_constructor_706
      (coe du_reg'45'below_1762)
      (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.ArchCorrectness.X86-64._.reg-below
d_reg'45'below_1762 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
d_reg'45'below_1762 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reg'45'below_1762 v9
du_reg'45'below_1762 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
du_reg'45'below_1762 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.ArchCorrectness.X86-64.entry-regtag
d_entry'45'regtag_1776 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_472
d_entry'45'regtag_1776 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_entry'45'regtag_1776
du_entry'45'regtag_1776 ::
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_472
du_entry'45'regtag_1776
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.C_mkRegTagWF_484
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         erased)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         erased)
-- Once.Adequacy.ArchCorrectness.X86-64.entry-like
d_entry'45'like_1782 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_entry'45'like_1782 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_entry'45'like_1782
du_entry'45'like_1782 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_entry'45'like_1782
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
-- Once.Adequacy.ArchCorrectness.X86-64._.no-ptr
d_no'45'ptr_1794 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'ptr_1794 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.entry-inv
d_entry'45'inv_1814 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1036
d_entry'45'inv_1814 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.C_mkFlatInv_1070
      (coe du_entry'45'wf_1752)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe du_entry'45'regtag_1776)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_mkRunAt_384
         v8 (coe d_main'45'heap'45'moded_1702 v0 v1 v2 v3 v4 v5 v6 v7 v8)
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_reach'45'start_344
            (coe du_entry'45'like_1782)))
-- Once.Adequacy.ArchCorrectness.X86-64.Nof
d_Nof_1818 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer -> Integer
d_Nof_1818 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3552
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_3690
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'witness_2342
            (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
            (coe
               d_entry'45'frame'45'x86'45'64_1504 (coe v0) (coe v1) (coe v2)
               (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
            (coe
               MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
               (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
            (coe v8)
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_5544
               (coe v0)
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v8))
            (coe v9)))
-- Once.Adequacy.ArchCorrectness.X86-64.conc-fuel
d_conc'45'fuel_1830
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.conc-fuel"
-- Once.Adequacy.ArchCorrectness.X86-64.conc-flat-sim-just
d_conc'45'flat'45'sim'45'just_1836 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_conc'45'flat'45'sim'45'just_1836 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.agree
d_agree_1846 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_agree_1846 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.du_events'45'agree_1442
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80)
      (coe
         MAlonzo.Code.Data.Nat.Base.C_constructor_120
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RegRoles.d_x86'45'64'45'roles_12)
      (coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (64 :: Integer)))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.du_x86'45'64'45'emitter_1890)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.du_x86'45'64'45'machine_1916)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.du_x86'45'64'45'traceloop_1918)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.du_x86'45'64'45'supply_3412
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
         (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.d_ret'45'no'45'wrap_268
            (coe v6))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.d_count'45'no'45'wrap_278
            (coe v6))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.d_tag'45'fits_328
            (coe v7))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.d_lit'45'fits_340
            (coe v7))
         (\ v10 v11 v12 v13 v14 v15 v16 v17 ->
            coe
              MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.du_float'45'fits_354
              v14)
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.d_lo'45'fits_288
            (coe v6)))
      (coe
         du_entry'45'view_1680
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_compile'45'trace_136
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_812
               (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v8))))
      (coe
         d_Nof_1818 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8) (coe v9))
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z64.d_ev'45'x86'45'64_362)
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z64.d_arith'45'env'45'x86'45'64_364
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_compile'45'trace_136
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_812
               (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v8))))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_812
         (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v8))
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45's_2298)
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'alloc_2288
            (coe
               d_entry'45'frame'45'x86'45'64_1504 (coe v0) (coe v1) (coe v2)
               (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_830
               (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v8)))
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72
            (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.Interface.d_initialState_30
         (coe du_as64_1550))
      (coe du_entry'45'corr_1706)
      (coe
         d_entry'45'inv_1814 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7) (coe v8))
-- Once.Adequacy.ArchCorrectness.X86-64.x86-64-conc-flat-sim
d_x86'45'64'45'conc'45'flat'45'sim_1856 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x86'45'64'45'conc'45'flat'45'sim_1856 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.asm-trace-correct-x86-64
d_asm'45'trace'45'correct'45'x86'45'64_1864 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_asm'45'trace'45'correct'45'x86'45'64_1864 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.x86-64-correct
d_x86'45'64'45'correct_1880 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_436 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_370 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_362 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_656 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_224 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_292 ->
  MAlonzo.Code.Once.Adequacy.Compile.T_ArchCorrect_48
d_x86'45'64'45'correct_1880 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_flat'45'from'45'obs_2474
      (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
      (coe
         d_entry'45'frame'45'x86'45'64_1504 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_5544
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308))
-- Once.Adequacy.ArchCorrectness.X86-64._.RunAt
d_RunAt_23717 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
