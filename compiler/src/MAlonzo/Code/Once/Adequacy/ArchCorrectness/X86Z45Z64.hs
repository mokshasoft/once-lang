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
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext
import qualified MAlonzo.Code.Once.Adequacy.CPU
import qualified MAlonzo.Code.Once.Adequacy.CPU.Interface
import qualified MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z64
import qualified MAlonzo.Code.Once.Adequacy.Compile
import qualified MAlonzo.Code.Once.Adequacy.FlatEvents
import qualified MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
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
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Memory.StackSlots
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Target.Arch

-- Once.Adequacy.ArchCorrectness.X86-64._.IRObsCorrectFlatness.ir-obs-correct
d_ir'45'obs'45'correct_44 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_536 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1056 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1004
d_ir'45'obs'45'correct_44 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_1820
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.ir-stack-budget
d_ir'45'stack'45'budget_80 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget_80 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_702
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.ir-to-trace
d_ir'45'to'45'trace_82 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
d_ir'45'to'45'trace_82 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_684
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.program-bound
d_program'45'bound_88
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.program-bound"
-- Once.Adequacy.ArchCorrectness.X86-64._.ir-obs-correct
d_ir'45'obs'45'correct_96 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_536 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1056 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1004
d_ir'45'obs'45'correct_96 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_1820
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
      (coe d_program'45'bound_88 v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.AsmTraceCorrect
d_AsmTraceCorrect_106 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
   Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  ()
d_AsmTraceCorrect_106 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.asm-sem
d_asm'45'sem_108 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_asm'45'sem_108 ~v0 = du_asm'45'sem_108
du_asm'45'sem_108 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_asm'45'sem_108
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_asm'45'sem_732
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-alloc
d_entry'45'alloc_110 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_entry'45'alloc_110 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.d_entry'45'alloc_742
      (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
      (coe d_program'45'bound_88 v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-bf
d_entry'45'bf_112 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_entry'45'bf_112 ~v0 = du_entry'45'bf_112
du_entry'45'bf_112 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_entry'45'bf_112 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'bf_766
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-frame
d_entry'45'frame_114 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14
d_entry'45'frame_114 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.d_entry'45'frame_736
      v0 (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308
      (MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
      (coe d_program'45'bound_88 v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-loc
d_entry'45'loc_116 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_entry'45'loc_116 ~v0 = du_entry'45'loc_116
du_entry'45'loc_116 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_entry'45'loc_116
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'loc_748
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-nh
d_entry'45'nh_118 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'nh_118 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-ns
d_entry'45'ns_120 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'ns_120 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-regs
d_entry'45'regs_122 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_126
d_entry'45'regs_122 ~v0 = du_entry'45'regs_122
du_entry'45'regs_122 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_126
du_entry'45'regs_122
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'regs_750
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-s
d_entry'45's_124 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_entry'45's_124 ~v0 = du_entry'45's_124
du_entry'45's_124 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_entry'45's_124
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45's_752
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-size
d_entry'45'size_126 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_entry'45'size_126 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.d_entry'45'size_740
      v0 (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308
      (MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
      (coe d_program'45'bound_88 v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.entry-witness
d_entry'45'witness_128 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_536 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1056 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1004) ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1004
d_entry'45'witness_128 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.d_entry'45'witness_772
      (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
      (coe d_program'45'bound_88 v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.flat-from-obs
d_flat'45'from'45'obs_130 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_536 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1056 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1004) ->
  (MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Adequacy.Compile.T_ArchCorrect_46
d_flat'45'from'45'obs_130 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_flat'45'from'45'obs_836
      (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
      (coe d_program'45'bound_88 v0) v1
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.flat-trace-of
d_flat'45'trace'45'of_132 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_536 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1056 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1004) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'trace'45'of_132 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.d_flat'45'trace'45'of_784
      (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
      (coe d_program'45'bound_88 v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FFOx.ir-flat-correct-of
d_ir'45'flat'45'correct'45'of_134 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_536 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1056 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1004) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'flat'45'correct'45'of_134 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.as64
d_as64_136 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10
d_as64_136 ~v0 = du_as64_136
du_as64_136 ::
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10
du_as64_136
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
      (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
-- Once.Adequacy.ArchCorrectness.X86-64.conc-trace
d_conc'45'trace_138 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_conc'45'trace_138 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Once.Adequacy.CPU.Interface.d_run'45'trace_34
             (coe du_as64_136)
             (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_compile'45'trace'45'cnt_68
                   (coe v0) (coe (0 :: Integer))
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_684
                      (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                      (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2))))
             (MAlonzo.Code.Once.Adequacy.CPU.Interface.d_initialState_30
                (coe du_as64_136))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe (\ v2 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.x86-64-loader-faithful
d_x86'45'64'45'loader'45'faithful_148
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.x86-64-loader-faithful"
-- Once.Adequacy.ArchCorrectness.X86-64._.flat-events
d_flat'45'events_156 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'events_156 ~v0 = du_flat'45'events_156
du_flat'45'events_156 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_flat'45'events_156
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_286
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
-- Once.Adequacy.ArchCorrectness.X86-64.x86-64-heap-room
d_x86'45'64'45'heap'45'room_168
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.x86-64-heap-room"
-- Once.Adequacy.ArchCorrectness.X86-64._.CompiledCorr
d_CompiledCorr_172 a0 a1 a2 a3 a4 = ()
-- Once.Adequacy.ArchCorrectness.X86-64._.EntryLike
d_EntryLike_176 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_EntryLike_176 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatInv
d_FlatInv_178 a0 a1 a2 a3 a4 = ()
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView
d_HeapView_182 a0 = ()
-- Once.Adequacy.ArchCorrectness.X86-64._.Reachable
d_Reachable_186 a0 a1 a2 a3 = ()
-- Once.Adequacy.ArchCorrectness.X86-64._.CompiledCorr.dataCorr
d_dataCorr_206 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dataCorr_206 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.d_dataCorr_524
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.CompiledCorr.pc-off
d_pc'45'off_208 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pc'45'off_208 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatInv.inv-env
d_inv'45'env_212 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv'45'env_212 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatInv.inv-ev
d_inv'45'ev_214 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.T_FlatInv_998 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv'45'ev_214 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatInv.inv-regtag
d_inv'45'regtag_216 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.T_FlatInv_998 ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_314
d_inv'45'regtag_216 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.d_inv'45'regtag_1020
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatInv.inv-run
d_inv'45'run_218 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.T_FlatInv_998 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_212
d_inv'45'run_218 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.d_inv'45'run_1026
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatInv.inv-wf
d_inv'45'wf_220 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.T_FlatInv_998 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506
d_inv'45'wf_220 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.d_inv'45'wf_1018
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.HDom
d_HDom_224 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> ()
d_HDom_224 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.dom-below
d_dom'45'below_226 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_226 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'below_262
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.front-lo
d_front'45'lo_228 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo_228 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_front'45'lo_266
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.haddr
d_haddr_230 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_haddr_230 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_haddr_244
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.haddr-inj
d_haddr'45'inj_232 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_232 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.haddr-suc
d_haddr'45'suc_234 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_234 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.hfront
d_hfront_236 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer
d_hfront_236 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_hfront_248
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.HeapView.lo
d_lo_238 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer
d_lo_238 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_lo_264
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatWF
d_FlatWF_248 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_FlatWF_248 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.sv-below
d_sv'45'below_250 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_sv'45'below_250 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.FlatRegTag
d_FlatRegTag_254 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_FlatRegTag_254 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.entry-view
d_entry'45'view_256 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218
d_entry'45'view_256 ~v0 = du_entry'45'view_256
du_entry'45'view_256 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218
du_entry'45'view_256
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.C_mkHV_268
      (\ v0 ->
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_slot'45'to'45'disp_10
           (coe
              MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50 (coe v0)))
      (0 :: Integer) erased
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_stack'45'top_244
      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
-- Once.Adequacy.ArchCorrectness.X86-64._.suc-law
d_suc'45'law_264 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45'law_264 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.main-heap-moded
d_main'45'heap'45'moded_276
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.main-heap-moded"
-- Once.Adequacy.ArchCorrectness.X86-64.entry-frame-base
d_entry'45'frame'45'base_278
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.entry-frame-base"
-- Once.Adequacy.ArchCorrectness.X86-64.entry-corr
d_entry'45'corr_282 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510
d_entry'45'corr_282 ~v0 ~v1 = du_entry'45'corr_282
du_entry'45'corr_282 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_510
du_entry'45'corr_282
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.C_constructor_528
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.C_constructor_460
         erased erased erased
         (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_stack'45'top_244))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_stack'45'top_244))
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
-- Once.Adequacy.ArchCorrectness.X86-64.entry-wf
d_entry'45'wf_304 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506
d_entry'45'wf_304 ~v0 ~v1 = du_entry'45'wf_304
du_entry'45'wf_304 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_506
du_entry'45'wf_304
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.C_constructor_548
      (coe du_reg'45'below_314)
      (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.ArchCorrectness.X86-64._.reg-below
d_reg'45'below_314 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
d_reg'45'below_314 ~v0 ~v1 v2 = du_reg'45'below_314 v2
du_reg'45'below_314 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
du_reg'45'below_314 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.ArchCorrectness.X86-64.entry-regtag
d_entry'45'regtag_328 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_314
d_entry'45'regtag_328 ~v0 ~v1 = du_entry'45'regtag_328
du_entry'45'regtag_328 ::
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_314
du_entry'45'regtag_328
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.C_mkRegTagWF_326
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         erased)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         erased)
-- Once.Adequacy.ArchCorrectness.X86-64.entry-like
d_entry'45'like_334 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_entry'45'like_334 ~v0 ~v1 = du_entry'45'like_334
du_entry'45'like_334 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_entry'45'like_334
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
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)))))))
-- Once.Adequacy.ArchCorrectness.X86-64._.no-ptr
d_no'45'ptr_346 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'ptr_346 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.entry-inv
d_entry'45'inv_368 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.T_FlatInv_998
d_entry'45'inv_368 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.C_mkFlatInv_1028
      (coe du_entry'45'wf_304) (coe du_entry'45'regtag_328)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_mkRunAt_234
         v1 (coe d_main'45'heap'45'moded_276 v0 v1)
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.C_reach'45'start_194
            (coe du_entry'45'like_334)))
-- Once.Adequacy.ArchCorrectness.X86-64.Nof
d_Nof_372 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer -> Integer
d_Nof_372 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_traces'45'agree_1036
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.d_entry'45'witness_772
            (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
            (coe
               MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
               (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
            (coe d_program'45'bound_88 v0) (coe v1)
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_1820
               (coe v0)
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
               (coe d_program'45'bound_88 v0)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v1)))
         v2)
-- Once.Adequacy.ArchCorrectness.X86-64.conc-fuel
d_conc'45'fuel_384
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.X86-64.conc-fuel"
-- Once.Adequacy.ArchCorrectness.X86-64.conc-flat-sim-just
d_conc'45'flat'45'sim'45'just_390 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_conc'45'flat'45'sim'45'just_390 = erased
-- Once.Adequacy.ArchCorrectness.X86-64._.agree
d_agree_400 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_agree_400 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ConcFlatSim.du_events'45'agree_4274
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
      (coe d_x86'45'64'45'heap'45'room_168 v0) (coe du_entry'45'view_256)
      (coe d_Nof_372 (coe v0) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z64.d_ev'45'x86'45'64_268)
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z64.d_arith'45'env'45'x86'45'64_270
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_compile'45'trace_160
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_684
               (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v1))))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_684
         (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_84
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45's_752)
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.d_entry'45'alloc_742
            (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
            (coe
               MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
               (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
            (coe d_program'45'bound_88 v0)
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_702
               (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v1)))
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74
            (coe (0 :: Integer))))
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.Interface.d_initialState_30
         (coe du_as64_136))
      (coe du_entry'45'corr_282)
      (coe d_entry'45'inv_368 (coe v0) (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.x86-64-conc-flat-sim
d_x86'45'64'45'conc'45'flat'45'sim_410 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x86'45'64'45'conc'45'flat'45'sim_410 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.asm-trace-correct-x86-64
d_asm'45'trace'45'correct'45'x86'45'64_418 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_asm'45'trace'45'correct'45'x86'45'64_418 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.x86-64-correct
d_x86'45'64'45'correct_428 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.Compile.T_ArchCorrect_46
d_x86'45'64'45'correct_428 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_flat'45'from'45'obs_836
      (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
      (coe d_program'45'bound_88 v0)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_1820
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.FrameInstantiation.d_x86'45'64'45'frame'45'semantics_308)
         (coe d_program'45'bound_88 v0))
-- Once.Adequacy.ArchCorrectness.X86-64._.RunAt
d_RunAt_1507 a0 a1 a2 = ()
