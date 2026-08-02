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
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation
import qualified MAlonzo.Code.Once.Adequacy.CPU
import qualified MAlonzo.Code.Once.Adequacy.CPU.Interface
import qualified MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z64
import qualified MAlonzo.Code.Once.Adequacy.Compile
import qualified MAlonzo.Code.Once.Adequacy.FlatEvents
import qualified MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF
import qualified MAlonzo.Code.Once.CCC.Machine.FlatStoreWF
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Memory.StackSlots
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Target.Arch

-- Once.Adequacy.ArchCorrectness.X86-64.program-bound
d_program'45'bound_8
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.program-bound"
-- Once.Adequacy.ArchCorrectness.X86-64._.MachineRefinesObsF
d_MachineRefinesObsF_12 a0 a1 a2 a3 a4 a5 = ()
-- Once.Adequacy.ArchCorrectness.X86-64._.ir-obs-correct
d_ir'45'obs'45'correct_16 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_530 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_382 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_330
d_ir'45'obs'45'correct_16
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_1146
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
      (coe d_program'45'bound_8)
-- Once.Adequacy.ArchCorrectness.X86-64._.MachineRefinesObsF.traces-agree
d_traces'45'agree_20 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_330 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_traces'45'agree_20 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_traces'45'agree_362
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.MachineRefinesObsF.value-realized
d_value'45'realized_22 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_330 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_value'45'realized_22 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_value'45'realized_370
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.AsmTraceCorrect
d_AsmTraceCorrect_26 ::
  (Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
   Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  ()
d_AsmTraceCorrect_26 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.asm-sem
d_asm'45'sem_28 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_asm'45'sem_28
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_asm'45'sem_84
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-alloc
d_entry'45'alloc_30 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_entry'45'alloc_30
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.d_entry'45'alloc_94
      (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
      (coe d_program'45'bound_8)
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-bf
d_entry'45'bf_32 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_entry'45'bf_32
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'bf_116
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-frame
d_entry'45'frame_34 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14
d_entry'45'frame_34
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.d_entry'45'frame_88
      (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308
      (MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
      d_program'45'bound_8
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-loc
d_entry'45'loc_36 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_entry'45'loc_36
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'loc_98
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-nh
d_entry'45'nh_38 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'nh_38 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-ns
d_entry'45'ns_40 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'ns_40 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-regs
d_entry'45'regs_42 ::
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_126
d_entry'45'regs_42
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'regs_100
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-s
d_entry'45's_44 ::
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_entry'45's_44
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45's_104
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-size
d_entry'45'size_46 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_entry'45'size_46
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.d_entry'45'size_92
      (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308
      (MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
      d_program'45'bound_8
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-witness
d_entry'45'witness_48 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_530 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_382 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_330) ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_330
d_entry'45'witness_48
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.d_entry'45'witness_124
      (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
      (coe d_program'45'bound_8)
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.flat-from-obs
d_flat'45'from'45'obs_50 ::
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_530 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_382 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_330) ->
  (MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Adequacy.Compile.T_ArchCorrect_46
d_flat'45'from'45'obs_50 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_flat'45'from'45'obs_188
      (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
      (coe d_program'45'bound_8) v0
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.flat-trace-of
d_flat'45'trace'45'of_52 ::
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_530 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_382 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_330) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'trace'45'of_52
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.d_flat'45'trace'45'of_136
      (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
      (coe d_program'45'bound_8)
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.ir-flat-correct-of
d_ir'45'flat'45'correct'45'of_54 ::
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_530 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_382 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_330) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'flat'45'correct'45'of_54 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.as64
d_as64_56 ::
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10
d_as64_56
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
      (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
-- Once.Adequacy.ArchCorrectness.X86-64.conc-trace
d_conc'45'trace_58 ::
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_conc'45'trace_58 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             MAlonzo.Code.Once.Adequacy.CPU.Interface.d_run'45'trace_34
             d_as64_56
             (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_compile'45'trace'45'cnt_62
                   (coe (0 :: Integer))
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_724
                      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                      (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v1))))
             (MAlonzo.Code.Once.Adequacy.CPU.Interface.d_initialState_30
                (coe d_as64_56))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe (\ v1 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.x86-64-loader-faithful
d_x86'45'64'45'loader'45'faithful_68
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.x86-64-loader-faithful"
-- Once.Adequacy.ArchCorrectness.X86-64._.flat-events
d_flat'45'events_76 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'events_76
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
-- Once.Adequacy.ArchCorrectness.X86-64._.CompiledCorr
d_CompiledCorr_80 a0 a1 a2 a3 = ()
-- Once.Adequacy.ArchCorrectness.X86-64._.EntryLike
d_EntryLike_84 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_EntryLike_84 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatInv
d_FlatInv_86 a0 a1 a2 a3 = ()
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView
d_HeapView_90 = ()
-- Once.Adequacy.ArchCorrectness.X86-64._.Reachable
d_Reachable_94 a0 a1 a2 = ()
-- Once.Adequacy.ArchCorrectness.X86-64._.events-agree
d_events'45'agree_96 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_168 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_432 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.T_FlatInv_848 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_events'45'agree_96
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.du_events'45'agree_3454
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
-- Once.Adequacy.ArchCorrectness.X86-64._.inv-env
d_inv'45'env_98 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.T_FlatInv_848 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv'45'env_98 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.inv-ev
d_inv'45'ev_100 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.T_FlatInv_848 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv'45'ev_100 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.inv-regtag
d_inv'45'regtag_102 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.T_FlatInv_848 ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_264
d_inv'45'regtag_102 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.d_inv'45'regtag_870
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.inv-run
d_inv'45'run_104 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.T_FlatInv_848 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.T_RunAt_812
d_inv'45'run_104 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.d_inv'45'run_876
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.inv-wf
d_inv'45'wf_106 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.T_FlatInv_848 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_456
d_inv'45'wf_106 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.d_inv'45'wf_868
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.CompiledCorr.dataCorr
d_dataCorr_114 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_432 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_276
d_dataCorr_114 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.d_dataCorr_446
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.CompiledCorr.pc-off
d_pc'45'off_116 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_432 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pc'45'off_116 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatInv.inv-env
d_inv'45'env_120 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.T_FlatInv_848 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv'45'env_120 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatInv.inv-ev
d_inv'45'ev_122 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.T_FlatInv_848 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv'45'ev_122 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatInv.inv-regtag
d_inv'45'regtag_124 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.T_FlatInv_848 ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_264
d_inv'45'regtag_124 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.d_inv'45'regtag_870
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatInv.inv-run
d_inv'45'run_126 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.T_FlatInv_848 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.T_RunAt_812
d_inv'45'run_126 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.d_inv'45'run_876
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatInv.inv-wf
d_inv'45'wf_128 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.T_FlatInv_848 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_456
d_inv'45'wf_128 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.d_inv'45'wf_868
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.HDom
d_HDom_132 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> ()
d_HDom_132 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.dom-below
d_dom'45'below_134 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_134 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'below_212
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.front-lo
d_front'45'lo_136 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_168 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo_136 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_front'45'lo_216
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.haddr
d_haddr_138 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_haddr_138 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_haddr_194
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.haddr-inj
d_haddr'45'inj_140 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_140 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.haddr-suc
d_haddr'45'suc_142 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_168 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_142 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.hfront
d_hfront_144 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_168 ->
  Integer
d_hfront_144 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_hfront_198
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.lo
d_lo_146 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_168 ->
  Integer
d_lo_146 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_lo_214
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatWF
d_FlatWF_156 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_FlatWF_156 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.sv-below
d_sv'45'below_158 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_sv'45'below_158 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatRegTag
d_FlatRegTag_162 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_FlatRegTag_162 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.entry-view
d_entry'45'view_164 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_168
d_entry'45'view_164
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.C_mkHV_218
      (\ v0 ->
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_slot'45'to'45'disp_10
           (coe
              MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50 (coe v0)))
      (0 :: Integer) erased
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_stack'45'top_244
      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
-- Once.Adequacy.ArchCorrectness.X86-64._.suc-law
d_suc'45'law_172 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45'law_172 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.entry-frame-base
d_entry'45'frame'45'base_182
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.entry-frame-base"
-- Once.Adequacy.ArchCorrectness.X86-64.entry-corr
d_entry'45'corr_186 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_432
d_entry'45'corr_186 ~v0 = du_entry'45'corr_186
du_entry'45'corr_186 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_432
du_entry'45'corr_186
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.C_constructor_450
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.C_constructor_372
         erased erased erased
         (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_stack'45'top_244)))
-- Once.Adequacy.ArchCorrectness.X86-64.entry-wf
d_entry'45'wf_208 ::
  Integer -> MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_456
d_entry'45'wf_208 ~v0 = du_entry'45'wf_208
du_entry'45'wf_208 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_456
du_entry'45'wf_208
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.C_constructor_498
      (coe du_reg'45'below_218)
      (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.ArchCorrectness.X86-64._.reg-below
d_reg'45'below_218 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
d_reg'45'below_218 ~v0 v1 = du_reg'45'below_218 v1
du_reg'45'below_218 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
du_reg'45'below_218 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.ArchCorrectness.X86-64.entry-regtag
d_entry'45'regtag_232 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_264
d_entry'45'regtag_232 ~v0 = du_entry'45'regtag_232
du_entry'45'regtag_232 ::
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_264
du_entry'45'regtag_232
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.C_mkRegTagWF_276
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         erased)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         erased)
-- Once.Adequacy.ArchCorrectness.X86-64.entry-like
d_entry'45'like_238 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_entry'45'like_238 ~v0 = du_entry'45'like_238
du_entry'45'like_238 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_entry'45'like_238
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
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))))))
-- Once.Adequacy.ArchCorrectness.X86-64._.no-ptr
d_no'45'ptr_250 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'ptr_250 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.entry-inv
d_entry'45'inv_272 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.T_FlatInv_848
d_entry'45'inv_272 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.C_mkFlatInv_878
      (coe du_entry'45'wf_208) (coe du_entry'45'regtag_232)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.C_mkRunAt_830
         v0
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.C_reach'45'start_794
            (coe du_entry'45'like_238)))
-- Once.Adequacy.ArchCorrectness.X86-64.Nof
d_Nof_276 :: MAlonzo.Code.Once.IR.T_IR_16 -> Integer -> Integer
d_Nof_276 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_traces'45'agree_362
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.d_entry'45'witness_124
            (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
            (coe
               MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
               (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
            (coe d_program'45'bound_8) (coe v0)
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_1146
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
               (coe d_program'45'bound_8) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v0)))
         v1)
-- Once.Adequacy.ArchCorrectness.X86-64.conc-fuel
d_conc'45'fuel_288
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.conc-fuel"
-- Once.Adequacy.ArchCorrectness.X86-64.conc-flat-sim-just
d_conc'45'flat'45'sim'45'just_294 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_conc'45'flat'45'sim'45'just_294 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.agree
d_agree_304 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_agree_304 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.du_events'45'agree_3454
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
      (coe d_entry'45'view_164) (coe d_Nof_276 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z64.d_ev'45'x86'45'64_268)
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z64.d_arith'45'env'45'x86'45'64_270
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_compile'45'trace_146
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_724
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v0))))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_724
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlat_76
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45's_104
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_742
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v0)))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.d_entry'45'alloc_94
            (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
            (coe
               MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
               (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
            (coe d_program'45'bound_8))
         (coe (0 :: Integer)))
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.Interface.d_initialState_30
         (coe d_as64_56))
      (coe du_entry'45'corr_186) (coe d_entry'45'inv_272 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.x86-64-conc-flat-sim
d_x86'45'64'45'conc'45'flat'45'sim_314 ::
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x86'45'64'45'conc'45'flat'45'sim_314 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.asm-trace-correct-x86-64
d_asm'45'trace'45'correct'45'x86'45'64_322 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_asm'45'trace'45'correct'45'x86'45'64_322 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.x86-64-correct
d_x86'45'64'45'correct_332 ::
  MAlonzo.Code.Once.Adequacy.Compile.T_ArchCorrect_46
d_x86'45'64'45'correct_332
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_flat'45'from'45'obs_188
      (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
      (coe d_program'45'bound_8)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_1146
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
         (coe d_program'45'bound_8))
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatState
d_FlatState_383 = ()
-- Once.Adequacy.ArchCorrectness.X86-64._.RunAt
d_RunAt_385 a0 a1 = ()
