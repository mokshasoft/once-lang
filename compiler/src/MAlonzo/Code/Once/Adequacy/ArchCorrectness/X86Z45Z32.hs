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
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimX86Z45Z32
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ConcFlatSim
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.RegRoles
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds
import qualified MAlonzo.Code.Once.Adequacy.CPU
import qualified MAlonzo.Code.Once.Adequacy.CPU.Interface
import qualified MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z32
import qualified MAlonzo.Code.Once.Adequacy.FlatEvents
import qualified MAlonzo.Code.Once.Arith.Backend.CallAnswer
import qualified MAlonzo.Code.Once.Arith.Backend.RunTraceCore
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Dispatch
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.RunTrace
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
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.AbstractToX86Z45Z32
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.FrameInstantiation
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Behavior
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Memory.StackSlots
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg
import qualified MAlonzo.Code.Once.Word

-- Once.Adequacy.ArchCorrectness.X86-32.x86-32-frame-semantics
d_x86'45'32'45'frame'45'semantics_32 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6
d_x86'45'32'45'frame'45'semantics_32 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                     ~v8 ~v9
  = du_x86'45'32'45'frame'45'semantics_32 v2
du_x86'45'32'45'frame'45'semantics_32 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6
du_x86'45'32'45'frame'45'semantics_32 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.FrameInstantiation.d_x86'45'32'45'frame'45'semantics_308
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.IRObsCorrectFlatness.ir-obs-correct
d_ir'45'obs'45'correct_460 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
d_ir'45'obs'45'correct_460 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_ir'45'obs'45'correct_460 v0 v1
du_ir'45'obs'45'correct_460 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
du_ir'45'obs'45'correct_460 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_6082
      (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.X86-32._.ir-obs-correct
d_ir'45'obs'45'correct_1794 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
d_ir'45'obs'45'correct_1794 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_ir'45'obs'45'correct_1794 v0 v1 v2
du_ir'45'obs'45'correct_1794 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
du_ir'45'obs'45'correct_1794 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_6082
      (coe v0) (coe v1)
      (coe du_x86'45'32'45'frame'45'semantics_32 (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-32.stack-top-in-stack
d_stack'45'top'45'in'45'stack_1844
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-32.stack-top-in-stack"
-- Once.Adequacy.ArchCorrectness.X86-32.entry-frame-x86-32
d_entry'45'frame'45'x86'45'32_1846 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14
d_entry'45'frame'45'x86'45'32_1846 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Memory.StackSlots.C_stack'45'addr_24
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_stack'45'top_322)
      (coe
         d_stack'45'top'45'in'45'stack_1844 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9)
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.BlockRunsT
d_BlockRunsT_1850 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  ()
d_BlockRunsT_1850 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.IOC
d_IOC_1852 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  ()
d_IOC_1852 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.blocks-prefix
d_blocks'45'prefix_1854 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_blocks'45'prefix_1854 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_blocks'45'prefix_1854
du_blocks'45'prefix_1854 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_blocks'45'prefix_1854 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_blocks'45'prefix_2864
      v2 v3
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-alloc
d_entry'45'alloc_1856 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_entry'45'alloc_1856 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'alloc_2750
      (coe
         d_entry'45'frame'45'x86'45'32_1846 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9))
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-bf
d_entry'45'bf_1858 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_entry'45'bf_1858 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_entry'45'bf_1858
du_entry'45'bf_1858 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_entry'45'bf_1858 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'bf_2774
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-blocks
d_entry'45'blocks_1860 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_entry'45'blocks_1860 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_entry'45'blocks_1860 v0 v1 v2
du_entry'45'blocks_1860 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_entry'45'blocks_1860 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'blocks_2934
      (coe v0) (coe v1)
      (coe du_x86'45'32'45'frame'45'semantics_32 (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-labels
d_entry'45'labels_1862 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'labels_1862 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-loc
d_entry'45'loc_1864 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_entry'45'loc_1864 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_entry'45'loc_1864
du_entry'45'loc_1864 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_entry'45'loc_1864
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'loc_2756
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-nh
d_entry'45'nh_1866 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'nh_1866 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-no-thunks
d_entry'45'no'45'thunks_1868 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny
d_entry'45'no'45'thunks_1868 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_entry'45'no'45'thunks_1868 v0 v2
du_entry'45'no'45'thunks_1868 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny
du_entry'45'no'45'thunks_1868 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'no'45'thunks_2808
      (coe v0) (coe du_x86'45'32'45'frame'45'semantics_32 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-ns
d_entry'45'ns_1870 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_entry'45'ns_1870 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_entry'45'ns_1870
du_entry'45'ns_1870 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_entry'45'ns_1870 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'ns_2770
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-regs
d_entry'45'regs_1872 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
d_entry'45'regs_1872 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_entry'45'regs_1872
du_entry'45'regs_1872 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
du_entry'45'regs_1872
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'regs_2758
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-s
d_entry'45's_1874 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_entry'45's_1874 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_entry'45's_1874
du_entry'45's_1874 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_entry'45's_1874
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45's_2760
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-span
d_entry'45'span_1876 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'span_1876 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-vr
d_entry'45'vr_1878 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   AgdaAny ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
    Integer ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784) ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600
d_entry'45'vr_1878 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'vr_2998
      (coe v0) (coe v1)
      (coe du_x86'45'32'45'frame'45'semantics_32 (coe v2))
      (coe
         d_entry'45'frame'45'x86'45'32_1846 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9))
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.entry-witness
d_entry'45'witness_1880 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
    Integer ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784) ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
d_entry'45'witness_1880 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'witness_2972
      (coe v0) (coe v1)
      (coe du_x86'45'32'45'frame'45'semantics_32 (coe v2))
      (coe
         d_entry'45'frame'45'x86'45'32_1846 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9))
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.flat-main
d_flat'45'main_1882 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   AgdaAny ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
    Integer ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784) ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_flat'45'main_1882 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_flat'45'main_3048
      (coe v0) (coe v1)
      (coe du_x86'45'32'45'frame'45'semantics_32 (coe v2))
      (coe
         d_entry'45'frame'45'x86'45'32_1846 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9))
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.flat-trace-fam
d_flat'45'trace'45'fam_1884 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   AgdaAny ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
    Integer ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784) ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_flat'45'trace'45'fam_1884 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_flat'45'trace'45'fam_3012
      (coe v0) (coe v1)
      (coe du_x86'45'32'45'frame'45'semantics_32 (coe v2))
      (coe
         d_entry'45'frame'45'x86'45'32_1846 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9))
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.fns-slot-stable
d_fns'45'slot'45'stable_1886 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_fns'45'slot'45'stable_1886 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_fns'45'slot'45'stable_1886 v2
du_fns'45'slot'45'stable_1886 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_fns'45'slot'45'stable_1886 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_fns'45'slot'45'stable_2944
      (coe du_x86'45'32'45'frame'45'semantics_32 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.image
d_image_1888 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_image_1888 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_image_1888 v0 v1
du_image_1888 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
du_image_1888 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_image_2824
      (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.image-slot-stable
d_image'45'slot'45'stable_1890 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_image'45'slot'45'stable_1890 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_image'45'slot'45'stable_1890 v0 v1 v2
du_image'45'slot'45'stable_1890 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_image'45'slot'45'stable_1890 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_image'45'slot'45'stable_2956
      (coe v0) (coe v1)
      (coe du_x86'45'32'45'frame'45'semantics_32 (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.ir-flat-correct-fam
d_ir'45'flat'45'correct'45'fam_1892 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   AgdaAny ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
    Integer ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784) ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'flat'45'correct'45'fam_1892 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.ir-flat-correct-main
d_ir'45'flat'45'correct'45'main_1894 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   AgdaAny ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
    Integer ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784) ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'flat'45'correct'45'main_1894 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.main-blocks
d_main'45'blocks_1896 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_main'45'blocks_1896 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_main'45'blocks_1896 v0 v1 v2
du_main'45'blocks_1896 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_main'45'blocks_1896 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_main'45'blocks_2820
      (coe v0) (coe v1)
      (coe du_x86'45'32'45'frame'45'semantics_32 (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.main-flat
d_main'45'flat_1898 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_main'45'flat_1898 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_main'45'flat_2962
      (coe v0) (coe du_x86'45'32'45'frame'45'semantics_32 (coe v2))
      (coe
         d_entry'45'frame'45'x86'45'32_1846 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9))
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.main-labels
d_main'45'labels_1900 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_main'45'labels_1900 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.main-span
d_main'45'span_1902 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_main'45'span_1902 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.span-prefix
d_span'45'prefix_1904 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_span'45'prefix_1904 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.start-flat
d_start'45'flat_1906 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_start'45'flat_1906 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_start'45'flat_2960
      (coe
         d_entry'45'frame'45'x86'45'32_1846 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9))
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.top-pre
d_top'45'pre_1908 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_top'45'pre_1908 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_top'45'pre_1908 v0 v1
du_top'45'pre_1908 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
du_top'45'pre_1908 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_top'45'pre_2814
      (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.X86-32.FFOx.σFS
d_σFS_1910 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_σFS_1910 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_σFS_1910 v2
du_σFS_1910 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_σFS_1910 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_σFS_2984
      (coe du_x86'45'32'45'frame'45'semantics_32 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-32.entry-frame-base
d_entry'45'frame'45'base_1912 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'frame'45'base_1912 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.as32
d_as32_1914 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10
d_as32_1914 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_as32_1914
du_as32_1914 ::
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10
du_as32_1914
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
      (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10)
-- Once.Adequacy.ArchCorrectness.X86-32._.flat-events
d_flat'45'events_1922 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_flat'45'events_1922 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_flat'45'events_1922 v2
du_flat'45'events_1922 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_flat'45'events_1922 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_464
      (coe du_x86'45'32'45'frame'45'semantics_32 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-32._.CompiledCorr
d_CompiledCorr_1926 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
  = ()
-- Once.Adequacy.ArchCorrectness.X86-32._.EntryLike
d_EntryLike_1930 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_EntryLike_1930 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._.HeapView
d_HeapView_1936 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Once.Adequacy.ArchCorrectness.X86-32._.Reachable
d_Reachable_1940 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
-- Once.Adequacy.ArchCorrectness.X86-32._.RunAt
d_RunAt_1942 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
-- Once.Adequacy.ArchCorrectness.X86-32._.CompiledCorr.code-eq
d_code'45'eq_1966 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'eq_1966 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._.CompiledCorr.dataCorr
d_dataCorr_1968 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_dataCorr_1968 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_690
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.CompiledCorr.pc-off
d_pc'45'off_1970 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pc'45'off_1970 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._.CompiledCorr.ret-eq
d_ret'45'eq_1972 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  AgdaAny
d_ret'45'eq_1972 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_ret'45'eq_694
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.HeapView.HDom
d_HDom_1992 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> ()
d_HDom_1992 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._.HeapView.caddr
d_caddr_1994 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_caddr_1994 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_caddr_498
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.HeapView.dom-below
d_dom'45'below_1996 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_1996 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'below_512
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.HeapView.front-lo
d_front'45'lo_1998 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo_1998 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_front'45'lo_516
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.HeapView.haddr
d_haddr_2000 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_haddr_2000 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_haddr_492
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.HeapView.haddr-inj
d_haddr'45'inj_2002 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_2002 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._.HeapView.haddr-suc
d_haddr'45'suc_2004 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_2004 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._.HeapView.hfront
d_hfront_2006 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer
d_hfront_2006 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_496
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.HeapView.lo
d_lo_2008 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer
d_lo_2008 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_514
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.RunAt.run-emit
d_run'45'emit_2018 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'emit_2018 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._.RunAt.run-ir
d_run'45'ir_2020 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_run'45'ir_2020 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_440
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.RunAt.run-linked
d_run'45'linked_2022 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'linked_2022 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'linked_444
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.RunAt.run-reach
d_run'45'reach_2024 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364
d_run'45'reach_2024 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'reach_446
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.RunAt.run-tbl
d_run'45'tbl_2026 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_run'45'tbl_2026 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'tbl_438
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-32._.FlatWF
d_FlatWF_2030 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_FlatWF_2030 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._.sv-below
d_sv'45'below_2032 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_sv'45'below_2032 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._.FlatRegTag
d_FlatRegTag_2036 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_FlatRegTag_2036 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.code-map
d_code'45'map_2038 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_code'45'map_2038 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
  = du_code'45'map_2038 v10 v11
du_code'45'map_2038 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
du_code'45'map_2038 v0 v1
  = coe
      du_pick_2048
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_find'45'label_406
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Label.C_callee_34
            (coe MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v1))))
-- Once.Adequacy.ArchCorrectness.X86-32._.pick
d_pick_2048 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer -> Integer
d_pick_2048 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_pick_2048 v12
du_pick_2048 :: Maybe Integer -> Integer
du_pick_2048 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-32.entry-view
d_entry'45'view_2052 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464
d_entry'45'view_2052 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_entry'45'view_2052 v10
du_entry'45'view_2052 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464
du_entry'45'view_2052 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.C_mkHV_518
      (\ v1 ->
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.AbstractToX86Z45Z32.d_slot'45'to'45'disp_164
           (coe
              MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50 (coe v1)))
      (0 :: Integer) (coe du_code'45'map_2038 (coe v0)) erased
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_stack'45'top_322
      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
-- Once.Adequacy.ArchCorrectness.X86-32._.suc-law
d_suc'45'law_2062 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45'law_2062 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.entry-corr
d_entry'45'corr_2074 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668
d_entry'45'corr_2074 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_entry'45'corr_2074
du_entry'45'corr_2074 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668
du_entry'45'corr_2074
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.C_constructor_702
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.C_constructor_1176
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
d_cong'45'pick_2086 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong'45'pick_2086 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.entry-wf
d_entry'45'wf_2120 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_720
d_entry'45'wf_2120 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_entry'45'wf_2120
du_entry'45'wf_2120 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_720
du_entry'45'wf_2120
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.C_constructor_762
      (coe du_reg'45'below_2130)
      (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.ArchCorrectness.X86-32._.reg-below
d_reg'45'below_2130 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
d_reg'45'below_2130 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11
  = du_reg'45'below_2130 v11
du_reg'45'below_2130 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
du_reg'45'below_2130 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.ArchCorrectness.X86-32.entry-regtag
d_entry'45'regtag_2144 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_528
d_entry'45'regtag_2144 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_entry'45'regtag_2144
du_entry'45'regtag_2144 ::
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_528
du_entry'45'regtag_2144
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.C_mkRegTagWF_540
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         erased)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         erased)
-- Once.Adequacy.ArchCorrectness.X86-32.entry-like
d_entry'45'like_2150 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_entry'45'like_2150 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_entry'45'like_2150
du_entry'45'like_2150 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_entry'45'like_2150
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
d_no'45'ptr_2162 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'ptr_2162 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.Nof
d_Nof_2182 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer -> Integer
d_Nof_2182 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3670
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_3814
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'witness_2972
            (coe v0) (coe v1)
            (coe du_x86'45'32'45'frame'45'semantics_32 (coe v2))
            (coe
               d_entry'45'frame'45'x86'45'32_1846 (coe v0) (coe v1) (coe v2)
               (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9))
            (coe v11)
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_6082
               (coe v0) (coe v1)
               (coe du_x86'45'32'45'frame'45'semantics_32 (coe v2))
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v11)
               (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v12)))
            (coe v10) (coe v13)))
-- Once.Adequacy.ArchCorrectness.X86-32.conc-run
d_conc'45'run_2192 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_conc'45'run_2192 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 v12
  = du_conc'45'run_2192 v0 v1 v2 v10 v11 v12
du_conc'45'run_2192 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_conc'45'run_2192 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events_36
      (coe
         (\ v6 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_halted_310
              (coe v6)))
      (coe
         (\ v6 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_pc_308
              (coe v6)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_fetch_668)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_execInstr_412)
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.RunTrace.d_matchCall_10)
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.RunTrace.d_ret'45'call_18
         (coe
            MAlonzo.Code.Once.Arith.Backend.CallAnswer.du_answer'45'at_220
            (coe v2)
            (coe
               MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z32.d_call'45'at'45'x86'45'32_12)))
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Dispatch.d_dispatch'45'arith_16
         (\ v6 v7 v8 ->
            coe
              MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimX86Z45Z32.du_val'45'x86'45'32_266
              v6 v7))
      (coe MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z32.d_ev'45'x86'45'32_10)
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z32.d_block'45'env_14
         (coe v3))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v5)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.AbstractToX86Z45Z32.d_compile'45'trace_294
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_image_2824
            (coe v0) (coe v1) (coe v4)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_initState_328)
-- Once.Adequacy.ArchCorrectness.X86-32.conc-fuel
d_conc'45'fuel_2212
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-32.conc-fuel"
-- Once.Adequacy.ArchCorrectness.X86-32.conc-flat-sim
d_conc'45'flat'45'sim_2224 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_conc'45'flat'45'sim_2224 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._.run₀
d_run'8320'_2242 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422
d_run'8320'_2242 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 v12 v13 ~v14 ~v15
  = du_run'8320'_2242 v1 v12 v13
du_run'8320'_2242 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422
du_run'8320'_2242 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_mkRunAt_448
      v0 v1 v2
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_reach'45'start_372
         (coe du_entry'45'like_2150))
-- Once.Adequacy.ArchCorrectness.X86-32._.agree
d_agree_2244 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_agree_2244 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.du_events'45'agree'45'start_4786
      (coe v0) (coe du_x86'45'32'45'frame'45'semantics_32 (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.d_slot'45'size_72)
      (coe
         MAlonzo.Code.Data.Nat.Base.C_constructor_120
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.RegRoles.d_x86'45'32'45'roles_12)
      (coe MAlonzo.Code.Once.Word.d_modulus_10 (coe (32 :: Integer)))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ConcFlatSim.du_x86'45'32'45'emitter_1594)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ConcFlatSim.du_x86'45'32'45'machine_1620)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ConcFlatSim.du_x86'45'32'45'traceloop_1630
         (coe du_x86'45'32'45'frame'45'semantics_32 (coe v2)))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ConcFlatSim.du_x86'45'32'45'supply_2122
         (coe v0) (coe du_x86'45'32'45'frame'45'semantics_32 (coe v2))
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.d_ret'45'no'45'wrap_274
            (coe v8))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.d_count'45'no'45'wrap_284
            (coe v8))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.d_tag'45'fits_334
            (coe v9))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.d_lit'45'fits_346
            (coe v9))
         (\ v16 v17 v18 v19 v20 v21 v22 v23 ->
            coe
              MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.du_float'45'fits_360
              v20)
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.d_lo'45'fits_294
            (coe v8)))
      (coe
         du_entry'45'view_2052
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.AbstractToX86Z45Z32.d_compile'45'trace_294
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_image_2824
               (coe v0) (coe v1) (coe v12))))
      (coe
         d_Nof_2182 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v12) (coe v13)
         (coe v15))
      (coe MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z32.d_ev'45'x86'45'32_10)
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z32.d_block'45'env_14
         (coe
            MAlonzo.Code.Once.Compile.d_blocks'45'x86'45'32_972 (coe v11)))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_image_2824
         (coe v0) (coe v1) (coe v12))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_start'45'flat_2960
         (coe
            d_entry'45'frame'45'x86'45'32_1846 (coe v0) (coe v1) (coe v2)
            (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_initState_328)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_824
         (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v12))
      (coe du_entry'45'corr_2074) (coe du_entry'45'wf_2120)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe du_entry'45'regtag_2144)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v14) erased))
      (coe du_run'8320'_2242 (coe v1) (coe v12) (coe v13))
-- Once.Adequacy.ArchCorrectness.X86-32.BlockRunsHyp-x86-32
d_BlockRunsHyp'45'x86'45'32_2246 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  ()
d_BlockRunsHyp'45'x86'45'32_2246 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.flat-x86-32
d_flat'45'x86'45'32_2250 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_flat'45'x86'45'32_2250 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_flat'45'main_3048
      (coe v0) (coe v1)
      (coe du_x86'45'32'45'frame'45'semantics_32 (coe v2))
      (coe
         d_entry'45'frame'45'x86'45'32_1846 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_6082
         (coe v0) (coe v1)
         (coe du_x86'45'32'45'frame'45'semantics_32 (coe v2)))
      (coe v10)
-- Once.Adequacy.ArchCorrectness.X86-32.ir-flat-correct-x86-32
d_ir'45'flat'45'correct'45'x86'45'32_2262 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'flat'45'correct'45'x86'45'32_2262 = erased
-- Once.Adequacy.ArchCorrectness.X86-32.file-flat-x86-32
d_file'45'flat'45'x86'45'32_2284 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078) ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.T_Image_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_file'45'flat'45'x86'45'32_2284 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._.p
d_p_2310 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078) ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.T_Image_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
d_p_2310 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12 ~v13
         v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_p_2310 v11 v14
du_p_2310 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
du_p_2310 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irProgram_390
      (coe MAlonzo.Code.Once.Compile.d_moduleTable_870 (coe v0)) (coe v1)
-- Once.Adequacy.ArchCorrectness.X86-32._.ir′
d_ir'8242'_2312 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078) ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.T_Image_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_ir'8242'_2312 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                ~v12 ~v13 v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_ir'8242'_2312 v11 v14
du_ir'8242'_2312 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_ir'8242'_2312 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.Program.d_main_388
      (coe
         MAlonzo.Code.Once.Compile.d_rewrite'45'program_896
         (coe du_p_2310 (coe v0) (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-32._.img
d_img_2314 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078) ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.T_Image_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_img_2314 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._._.img-at
d_img'45'at_2324 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078) ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.T_Image_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_img'45'at_2324 = erased
-- Once.Adequacy.ArchCorrectness.X86-32._.code-eq
d_code'45'eq_2326 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_AddrNoWrap_230 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.ResourceBounds.T_LitFits_298 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078) ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.T_Image_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'eq_2326 = erased
