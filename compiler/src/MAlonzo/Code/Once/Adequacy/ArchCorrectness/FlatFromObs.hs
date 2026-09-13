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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Adequacy.CPU.Interface
import qualified MAlonzo.Code.Once.Adequacy.Compile
import qualified MAlonzo.Code.Once.Adequacy.FlatEvents
import qualified MAlonzo.Code.Once.Adequacy.SourceTrace
import qualified MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable
import qualified MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas
import qualified MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Behavior
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Target.Arch

-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.BlockRuns
d_BlockRuns_26 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.IRObsCorrectF
d_IRObsCorrectF_38 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_38 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.InputAt
d_InputAt_40 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.MachineRefinesObsF
d_MachineRefinesObsF_42 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                        a13 a14 a15 a16 a17 a18 a19 a20
  = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.SpanAt
d_SpanAt_46 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> ()
d_SpanAt_46 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized
d_ValueRealized_48 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                   a14 a15 a16 a17 a18 a19 a20
  = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.emitted
d_emitted_72 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_emitted_72 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_emitted_72 v0
du_emitted_72 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_emitted_72 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.du_emitted_1362
      (coe v0) v3 v4 v5 v6 v7
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.BlockRuns.closures
d_closures_398 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_BlockRuns_1768 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_closures_398 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_closures_1776
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.BlockRuns.coalgs
d_coalgs_400 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_BlockRuns_1768 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_coalgs_400 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_coalgs_1778
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.MachineRefinesObsF.traces-agree
d_traces'45'agree_436 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1550 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_traces'45'agree_436 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.MachineRefinesObsF.value-realized
d_value'45'realized_438 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1550 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458
d_value'45'realized_438 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_value'45'realized_1580
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.at-end
d_at'45'end_658 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_658 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.cont-alloc
d_cont'45'alloc_660 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_cont'45'alloc_660 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_cont'45'alloc_1510
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.live
d_live_662 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_662 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.no-link
d_no'45'link_664 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_664 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.no-ret
d_no'45'ret_666 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_666 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.out-mode
d_out'45'mode_668 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_668 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_out'45'mode_1508
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.place
d_place_670 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_620
d_place_670 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_place_1522
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.run
d_run_672 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_run_672 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_run_1512 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.settle
d_settle_674 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_674 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_settle_1506
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.steps
d_steps_676 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458 ->
  Integer
d_steps_676 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_steps_1504
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ir-stack-budget
d_ir'45'stack'45'budget_680 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget_680 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_ir'45'stack'45'budget_680 v0
du_ir'45'stack'45'budget_680 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
du_ir'45'stack'45'budget_680 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_830
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ir-to-trace
d_ir'45'to'45'trace_682 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_ir'45'to'45'trace_682 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_ir'45'to'45'trace_682 v0
du_ir'45'to'45'trace_682 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_ir'45'to'45'trace_682 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_812
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.BlockRuns
d_BlockRuns_1384 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectF
d_IRObsCorrectF_1390 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_1390 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.MachineRefinesObsF
d_MachineRefinesObsF_1392 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                          a13 a14 a15 a16 a17 a18
  = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.SpanAt
d_SpanAt_1396 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> ()
d_SpanAt_1396 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized
d_ValueRealized_1398 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                     a14 a15 a16 a17 a18
  = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.emitted
d_emitted_1402 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_emitted_1402 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_emitted_1402 v0
du_emitted_1402 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_emitted_1402 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.du_emitted_1362
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.BlockRuns.closures
d_closures_1408 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_BlockRuns_1768 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_closures_1408 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_closures_1776
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.BlockRuns.coalgs
d_coalgs_1410 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_BlockRuns_1768 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_coalgs_1410 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_coalgs_1778
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.MachineRefinesObsF.traces-agree
d_traces'45'agree_1414 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1550 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_traces'45'agree_1414 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.MachineRefinesObsF.value-realized
d_value'45'realized_1416 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1550 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458
d_value'45'realized_1416 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_value'45'realized_1580
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.at-end
d_at'45'end_1420 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_1420 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.cont-alloc
d_cont'45'alloc_1422 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_cont'45'alloc_1422 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_cont'45'alloc_1510
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.live
d_live_1424 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_1424 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.no-link
d_no'45'link_1426 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_1426 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.no-ret
d_no'45'ret_1428 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_1428 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.out-mode
d_out'45'mode_1430 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_1430 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_out'45'mode_1508
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.place
d_place_1432 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_620
d_place_1432 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_place_1522
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.run
d_run_1434 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_run_1434 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_run_1512 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.settle
d_settle_1436 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_1436 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_settle_1506
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.steps
d_steps_1438 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458 ->
  Integer
d_steps_1438 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_steps_1504
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.BeforeFrontier
d_BeforeFrontier_1462 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs.asm-sem
d_asm'45'sem_1510 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_asm'45'sem_1510 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7
  = du_asm'45'sem_1510 v5 v7
du_asm'45'sem_1510 ::
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
du_asm'45'sem_1510 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.Interface.d_exec'45'bytes_40
      (coe v0)
      (coe MAlonzo.Code.Once.Adequacy.CPU.Interface.d_assemble_38 v0 v1)
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-size
d_entry'45'size_1516
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.FlatFromObs.entry-size"
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-alloc
d_entry'45'alloc_1518 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_entry'45'alloc_1518 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7
  = du_entry'45'alloc_1518 v4 v7
du_entry'45'alloc_1518 ::
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_entry'45'alloc_1518 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_588 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v1)
      (coe (0 :: Integer)) (coe (1 :: Integer))
      (coe (\ v2 -> 0 :: Integer))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-loc
d_entry'45'loc_1524 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_entry'45'loc_1524 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_entry'45'loc_1524
du_entry'45'loc_1524 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_entry'45'loc_1524
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
            (coe (0 :: Integer)))
         (coe (0 :: Integer)))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-regs
d_entry'45'regs_1526 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
d_entry'45'regs_1526 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_entry'45'regs_1526
du_entry'45'regs_1526 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
du_entry'45'regs_1526
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkRegs_144
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72
         (coe (0 :: Integer)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72
         (coe (0 :: Integer)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72
         (coe (0 :: Integer)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72
         (coe (0 :: Integer)))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-s
d_entry'45's_1528 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_entry'45's_1528 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_entry'45's_1528
du_entry'45's_1528 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_entry'45's_1528
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_422
      (coe du_entry'45'regs_1526)
      (coe (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      (coe (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-ns
d_entry'45'ns_1538 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_entry'45'ns_1538 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_entry'45'ns_1538
du_entry'45'ns_1538 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_entry'45'ns_1538 = coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-bf
d_entry'45'bf_1542 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_entry'45'bf_1542 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_entry'45'bf_1542
du_entry'45'bf_1542 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_entry'45'bf_1542
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_680
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-nh
d_entry'45'nh_1544 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'nh_1544 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-span
d_entry'45'span_1548 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'span_1548 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.block-runs
d_block'45'runs_1562
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.FlatFromObs.block-runs"
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-witness
d_entry'45'witness_1568 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_BlockRuns_1768 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1596 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1550) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1550
d_entry'45'witness_1568 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_entry'45'witness_1568 v0 v1 v2 v4 v5 v6 v7 v8 v9
du_entry'45'witness_1568 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_BlockRuns_1768 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1596 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1550) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1550
du_entry'45'witness_1568 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      v7 (coe d_entry'45'size_1516 v0 v1 v2 erased v3 v4 v5 v6)
      (0 :: Integer) (0 :: Integer)
      (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_812
         (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v6))
      (0 :: Integer)
      (MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'to'45'trace'45'slot'45'stable_876
         (coe v0) (coe v2) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v6))
      (coe d_block'45'runs_1562 v0 v1 v2 erased v3 v4 v5 v6) erased
      (coe MAlonzo.Code.Once.IR.C_Stack_6)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe du_entry'45's_1528)
      (coe
         du_entry'45'alloc_1518 (coe v3)
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_830
            (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v6)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72
         (coe (0 :: Integer)))
      (coe du_entry'45'ns_1538) erased
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.C_in'45'unit_1616)
      v8
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-vr
d_entry'45'vr_1586 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_BlockRuns_1768 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1596 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1550) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458
d_entry'45'vr_1586 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_entry'45'vr_1586 v0 v1 v2 v4 v5 v6 v7 v8 v9
du_entry'45'vr_1586 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_BlockRuns_1768 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1596 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1550) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_ValueRealized_1458
du_entry'45'vr_1586 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_value'45'realized_1580
      (coe
         du_entry'45'witness_1568 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4) (coe v5) (coe v6)
         (coe
            v7 (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16) v6)
         (coe v8))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.flat-trace-fam
d_flat'45'trace'45'fam_1600 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_BlockRuns_1768 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1596 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1550) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_flat'45'trace'45'fam_1600 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_flat'45'trace'45'fam_1600 v0 v1 v2 v4 v5 v6 v7 v8 v9
du_flat'45'trace'45'fam_1600 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_BlockRuns_1768 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1596 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1550) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_flat'45'trace'45'fam_1600 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> coe
             MAlonzo.Code.Data.List.Base.du_take_530 (coe v8)
             (coe
                MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_438 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_steps_1504
                   (coe
                      du_entry'45'vr_1586 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                      (coe v5) (coe v9) (coe v6) (coe v8)))
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_812
                   (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                   (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v9))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
                   (coe du_entry'45's_1528)
                   (coe
                      du_entry'45'alloc_1518 (coe v3)
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_830
                         (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v9)))
                   (coe (0 :: Integer))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72
                      (coe (0 :: Integer)))
                   (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatFromObs.AsmTraceCorrect
d_AsmTraceCorrect_1610 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  (Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6) ->
  ()
d_AsmTraceCorrect_1610 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.ir-flat-correct-fam
d_ir'45'flat'45'correct'45'fam_1632 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_BlockRuns_1768 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1596 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1550) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'flat'45'correct'45'fam_1632 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.flat-trace-of
d_flat'45'trace'45'of_1650 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_BlockRuns_1768 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1596 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1550) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_flat'45'trace'45'of_1650 v0 v1 v2 ~v3 v4 v5 v6 v7 v8
  = du_flat'45'trace'45'of_1650 v0 v1 v2 v4 v5 v6 v7 v8
du_flat'45'trace'45'of_1650 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_BlockRuns_1768 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1596 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1550) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
du_flat'45'trace'45'of_1650 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Denotation.Behavior.du_behavior'45'by_50
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_'10214'_'10215'IR_64
         (coe v7)
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_158
            (coe v2)))
      (coe
         du_flat'45'trace'45'fam_1600 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4) (coe v5) (coe v6) (coe v7))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.ir-flat-correct-of
d_ir'45'flat'45'correct'45'of_1670 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_BlockRuns_1768 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1596 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1550) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'flat'45'correct'45'of_1670 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.rewrite-preserves-of
d_rewrite'45'preserves'45'of_1690
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.FlatFromObs.rewrite-preserves-of"
-- Once.Adequacy.ArchCorrectness.FlatFromObs.flat-from-obs
d_flat'45'from'45'obs_1700 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_BlockRuns_1768 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1596 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1550) ->
  (MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Adequacy.Compile.T_ArchCorrect_48
d_flat'45'from'45'obs_1700 v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8
  = du_flat'45'from'45'obs_1700 v0 v1 v2 v4 v5 v6 v7
du_flat'45'from'45'obs_1700 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_BlockRuns_1768 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1596 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1550) ->
  MAlonzo.Code.Once.Adequacy.Compile.T_ArchCorrect_48
du_flat'45'from'45'obs_1700 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.C_constructor_118
      (coe du_asm'45'sem_1510 (coe v4))
      (coe
         du_flat'45'trace'45'of_1650 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4) (coe v5) (coe v6))
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.InputAt
d_InputAt_20269 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
