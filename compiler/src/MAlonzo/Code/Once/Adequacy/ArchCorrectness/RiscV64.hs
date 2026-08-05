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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64 where

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
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs
import qualified MAlonzo.Code.Once.Adequacy.CPU
import qualified MAlonzo.Code.Once.Adequacy.CPU.Interface
import qualified MAlonzo.Code.Once.Adequacy.Compile
import qualified MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.AbstractToRiscV
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.FrameInstantiation
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.StackSlots
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Target.Arch

-- Once.Adequacy.ArchCorrectness.RiscV64._.IRObsCorrectFlatness.ir-obs-correct
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
-- Once.Adequacy.ArchCorrectness.RiscV64.program-bound
d_program'45'bound_82
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.RiscV64.program-bound"
-- Once.Adequacy.ArchCorrectness.RiscV64._.ir-obs-correct
d_ir'45'obs'45'correct_86 ::
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
d_ir'45'obs'45'correct_86 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_1820
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.FrameInstantiation.d_rv64'45'frame'45'semantics_308)
      (coe d_program'45'bound_82 v0)
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.AsmTraceCorrect
d_AsmTraceCorrect_90 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
   Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  ()
d_AsmTraceCorrect_90 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.asm-sem
d_asm'45'sem_92 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_asm'45'sem_92 ~v0 = du_asm'45'sem_92
du_asm'45'sem_92 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_asm'45'sem_92
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_asm'45'sem_732
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_riscv64_12))
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.entry-alloc
d_entry'45'alloc_94 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_entry'45'alloc_94 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.d_entry'45'alloc_742
      (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_riscv64_12)
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.FrameInstantiation.d_rv64'45'frame'45'semantics_308)
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_riscv64_12))
      (coe d_program'45'bound_82 v0)
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.entry-bf
d_entry'45'bf_96 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_entry'45'bf_96 ~v0 = du_entry'45'bf_96
du_entry'45'bf_96 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_entry'45'bf_96 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'bf_766
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.entry-frame
d_entry'45'frame_98 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14
d_entry'45'frame_98 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.d_entry'45'frame_736
      v0 (coe MAlonzo.Code.Once.Target.Arch.C_riscv64_12)
      MAlonzo.Code.Once.CCC.Target.RiscV64.FrameInstantiation.d_rv64'45'frame'45'semantics_308
      (MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_riscv64_12))
      (coe d_program'45'bound_82 v0)
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.entry-loc
d_entry'45'loc_100 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_entry'45'loc_100 ~v0 = du_entry'45'loc_100
du_entry'45'loc_100 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_entry'45'loc_100
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'loc_748
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.entry-nh
d_entry'45'nh_102 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'nh_102 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.entry-ns
d_entry'45'ns_104 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'ns_104 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.entry-regs
d_entry'45'regs_106 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_126
d_entry'45'regs_106 ~v0 = du_entry'45'regs_106
du_entry'45'regs_106 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_126
du_entry'45'regs_106
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'regs_750
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.entry-s
d_entry'45's_108 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_entry'45's_108 ~v0 = du_entry'45's_108
du_entry'45's_108 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_entry'45's_108
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45's_752
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.entry-size
d_entry'45'size_110 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_entry'45'size_110 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.d_entry'45'size_740
      v0 (coe MAlonzo.Code.Once.Target.Arch.C_riscv64_12)
      MAlonzo.Code.Once.CCC.Target.RiscV64.FrameInstantiation.d_rv64'45'frame'45'semantics_308
      (MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_riscv64_12))
      (coe d_program'45'bound_82 v0)
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.entry-witness
d_entry'45'witness_112 ::
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
d_entry'45'witness_112 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.d_entry'45'witness_772
      (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_riscv64_12)
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.FrameInstantiation.d_rv64'45'frame'45'semantics_308)
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_riscv64_12))
      (coe d_program'45'bound_82 v0)
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.flat-from-obs
d_flat'45'from'45'obs_114 ::
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
d_flat'45'from'45'obs_114 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_flat'45'from'45'obs_836
      (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_riscv64_12)
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.FrameInstantiation.d_rv64'45'frame'45'semantics_308)
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_riscv64_12))
      (coe d_program'45'bound_82 v0) v1
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.flat-trace-of
d_flat'45'trace'45'of_116 ::
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
d_flat'45'trace'45'of_116 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.d_flat'45'trace'45'of_784
      (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_riscv64_12)
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.FrameInstantiation.d_rv64'45'frame'45'semantics_308)
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_riscv64_12))
      (coe d_program'45'bound_82 v0)
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.ir-flat-correct-of
d_ir'45'flat'45'correct'45'of_118 ::
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
d_ir'45'flat'45'correct'45'of_118 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.asR
d_asR_120 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10
d_asR_120 ~v0 = du_asR_120
du_asR_120 ::
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10
du_asR_120
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
      (coe MAlonzo.Code.Once.Target.Arch.C_riscv64_12)
-- Once.Adequacy.ArchCorrectness.RiscV64.conc-trace
d_conc'45'trace_122 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_conc'45'trace_122 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Once.Adequacy.CPU.Interface.d_run'45'trace_34
             (coe du_asR_120)
             (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.AbstractToRiscV.d_compile'45'trace'45'cnt_82
                   (coe v0) (coe (0 :: Integer))
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_684
                      (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                      (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2))))
             (MAlonzo.Code.Once.Adequacy.CPU.Interface.d_initialState_30
                (coe du_asR_120))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe (\ v2 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.RiscV64.riscv64-loader-faithful
d_riscv64'45'loader'45'faithful_132
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.RiscV64.riscv64-loader-faithful"
-- Once.Adequacy.ArchCorrectness.RiscV64.riscv64-conc-flat-sim
d_riscv64'45'conc'45'flat'45'sim_138
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.RiscV64.riscv64-conc-flat-sim"
-- Once.Adequacy.ArchCorrectness.RiscV64.asm-trace-correct-riscv64
d_asm'45'trace'45'correct'45'riscv64_140 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_asm'45'trace'45'correct'45'riscv64_140 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.riscv64-correct
d_riscv64'45'correct_150 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.Compile.T_ArchCorrect_46
d_riscv64'45'correct_150 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_flat'45'from'45'obs_836
      (coe v0) (coe MAlonzo.Code.Once.Target.Arch.C_riscv64_12)
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.FrameInstantiation.d_rv64'45'frame'45'semantics_308)
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
         (coe MAlonzo.Code.Once.Target.Arch.C_riscv64_12))
      (coe d_program'45'bound_82 v0)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_1820
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.FrameInstantiation.d_rv64'45'frame'45'semantics_308)
         (coe d_program'45'bound_82 v0))
