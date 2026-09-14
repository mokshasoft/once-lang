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
import qualified MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface
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
d_BlockRuns_32 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.IRObsCorrectF
d_IRObsCorrectF_64 ::
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
d_IRObsCorrectF_64 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.InputAt
d_InputAt_68 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.MachineRefinesObsF
d_MachineRefinesObsF_72 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                        a13 a14 a15 a16 a17 a18 a19 a20
  = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.SpanAt
d_SpanAt_84 ::
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
d_SpanAt_84 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized
d_ValueRealized_92 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                   a14 a15 a16 a17 a18 a19 a20
  = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.emitted
d_emitted_178 ::
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
d_emitted_178 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_emitted_178 v0
du_emitted_178 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_emitted_178 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_emitted_3326
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.BlockRuns.closures
d_closures_826 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3732 ->
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
d_closures_826 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_closures_3740
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.BlockRuns.coalgs
d_coalgs_828 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3732 ->
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
d_coalgs_828 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_coalgs_3742
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.MachineRefinesObsF.traces-agree
d_traces'45'agree_936 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_traces'45'agree_936 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.MachineRefinesObsF.value-realized
d_value'45'realized_938 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422
d_value'45'realized_938 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_3544
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.at-end
d_at'45'end_1212 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_1212 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.cont-alloc
d_cont'45'alloc_1214 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_cont'45'alloc_1214 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3474
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.live
d_live_1216 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_1216 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.no-link
d_no'45'link_1218 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_1218 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.no-ret
d_no'45'ret_1220 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_1220 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.out-mode
d_out'45'mode_1222 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_1222 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3472
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.place
d_place_1224 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_620
d_place_1224 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3486
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.run
d_run_1226 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_run_1226 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3476
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.settle
d_settle_1228 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_1228 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3470
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.steps
d_steps_1230 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  Integer
d_steps_1230 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3468
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ir-stack-budget
d_ir'45'stack'45'budget_1312 ::
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
d_ir'45'stack'45'budget_1312 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_ir'45'stack'45'budget_1312 v0
du_ir'45'stack'45'budget_1312 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
du_ir'45'stack'45'budget_1312 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_830
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ir-to-trace
d_ir'45'to'45'trace_1314 ::
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
d_ir'45'to'45'trace_1314 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_ir'45'to'45'trace_1314 v0
du_ir'45'to'45'trace_1314 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_ir'45'to'45'trace_1314 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_812
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.BlockRuns
d_BlockRuns_2016 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectF
d_IRObsCorrectF_2022 ::
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
d_IRObsCorrectF_2022 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.MachineRefinesObsF
d_MachineRefinesObsF_2024 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                          a13 a14 a15 a16 a17 a18
  = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.SpanAt
d_SpanAt_2028 ::
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
d_SpanAt_2028 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized
d_ValueRealized_2030 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                     a14 a15 a16 a17 a18
  = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.emitted
d_emitted_2034 ::
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
d_emitted_2034 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_emitted_2034 v0
du_emitted_2034 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_emitted_2034 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_emitted_3326
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.BlockRuns.closures
d_closures_2040 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3732 ->
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
d_closures_2040 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_closures_3740
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.BlockRuns.coalgs
d_coalgs_2042 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3732 ->
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
d_coalgs_2042 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_coalgs_3742
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.MachineRefinesObsF.traces-agree
d_traces'45'agree_2046 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_traces'45'agree_2046 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.MachineRefinesObsF.value-realized
d_value'45'realized_2048 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422
d_value'45'realized_2048 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_3544
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.at-end
d_at'45'end_2052 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_2052 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.cont-alloc
d_cont'45'alloc_2054 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_cont'45'alloc_2054 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3474
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.live
d_live_2056 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_2056 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.no-link
d_no'45'link_2058 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_2058 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.no-ret
d_no'45'ret_2060 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_2060 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.out-mode
d_out'45'mode_2062 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_2062 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3472
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.place
d_place_2064 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_620
d_place_2064 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3486
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.run
d_run_2066 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_run_2066 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3476
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.settle
d_settle_2068 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_2068 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3470
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.steps
d_steps_2070 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  Integer
d_steps_2070 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3468
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.BeforeFrontier
d_BeforeFrontier_2094 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs.asm-sem
d_asm'45'sem_2142 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_asm'45'sem_2142 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7
  = du_asm'45'sem_2142 v5 v7
du_asm'45'sem_2142 ::
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
du_asm'45'sem_2142 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.Interface.d_exec'45'bytes_40
      (coe v0)
      (coe MAlonzo.Code.Once.Adequacy.CPU.Interface.d_assemble_38 v0 v1)
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-size
d_entry'45'size_2148
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.FlatFromObs.entry-size"
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-alloc
d_entry'45'alloc_2150 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_entry'45'alloc_2150 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7
  = du_entry'45'alloc_2150 v4 v7
du_entry'45'alloc_2150 ::
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_entry'45'alloc_2150 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_588 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v1)
      (coe (0 :: Integer)) (coe (1 :: Integer))
      (coe (\ v2 -> 0 :: Integer))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-loc
d_entry'45'loc_2156 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_entry'45'loc_2156 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_entry'45'loc_2156
du_entry'45'loc_2156 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_entry'45'loc_2156
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
            (coe (0 :: Integer)))
         (coe (0 :: Integer)))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-regs
d_entry'45'regs_2158 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
d_entry'45'regs_2158 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_entry'45'regs_2158
du_entry'45'regs_2158 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
du_entry'45'regs_2158
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
d_entry'45's_2160 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_entry'45's_2160 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_entry'45's_2160
du_entry'45's_2160 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_entry'45's_2160
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_422
      (coe du_entry'45'regs_2158)
      (coe (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      (coe (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-ns
d_entry'45'ns_2170 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_entry'45'ns_2170 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_entry'45'ns_2170
du_entry'45'ns_2170 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_entry'45'ns_2170 = coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-bf
d_entry'45'bf_2174 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_entry'45'bf_2174 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_entry'45'bf_2174
du_entry'45'bf_2174 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_entry'45'bf_2174
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_680
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-nh
d_entry'45'nh_2176 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'nh_2176 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-span
d_entry'45'span_2180 ::
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
d_entry'45'span_2180 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.block-runs
d_block'45'runs_2194
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.FlatFromObs.block-runs"
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-witness
d_entry'45'witness_2200 ::
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3732 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
d_entry'45'witness_2200 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_entry'45'witness_2200 v0 v1 v2 v4 v5 v6 v7 v8 v9
du_entry'45'witness_2200 ::
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3732 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
du_entry'45'witness_2200 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      v7 (coe d_entry'45'size_2148 v0 v1 v2 erased v3 v4 v5 v6)
      (0 :: Integer) (0 :: Integer)
      (MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_812
         (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v6))
      (0 :: Integer)
      (MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'to'45'trace'45'slot'45'stable_876
         (coe v0) (coe v2) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v6))
      (coe d_block'45'runs_2194 v0 v1 v2 erased v3 v4 v5 v6) erased
      (coe MAlonzo.Code.Once.IR.C_Stack_6)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe du_entry'45's_2160)
      (coe
         du_entry'45'alloc_2150 (coe v3)
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_830
            (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v6)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72
         (coe (0 :: Integer)))
      (coe du_entry'45'ns_2170) erased
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'unit_3580)
      v8
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-vr
d_entry'45'vr_2218 ::
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3732 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422
d_entry'45'vr_2218 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_entry'45'vr_2218 v0 v1 v2 v4 v5 v6 v7 v8 v9
du_entry'45'vr_2218 ::
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3732 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422
du_entry'45'vr_2218 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_3544
      (coe
         du_entry'45'witness_2200 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4) (coe v5) (coe v6)
         (coe
            v7 (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16) v6)
         (coe v8))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.flat-trace-fam
d_flat'45'trace'45'fam_2232 ::
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3732 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_flat'45'trace'45'fam_2232 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_flat'45'trace'45'fam_2232 v0 v1 v2 v4 v5 v6 v7 v8 v9
du_flat'45'trace'45'fam_2232 ::
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3732 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_flat'45'trace'45'fam_2232 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> coe
             MAlonzo.Code.Data.List.Base.du_take_530 (coe v8)
             (coe
                MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_438 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3468
                   (coe
                      du_entry'45'vr_2218 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                      (coe v5) (coe v9) (coe v6) (coe v8)))
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_812
                   (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                   (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v9))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
                   (coe du_entry'45's_2160)
                   (coe
                      du_entry'45'alloc_2150 (coe v3)
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
d_AsmTraceCorrect_2242 ::
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
d_AsmTraceCorrect_2242 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.ir-flat-correct-fam
d_ir'45'flat'45'correct'45'fam_2264 ::
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3732 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'flat'45'correct'45'fam_2264 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.flat-trace-of
d_flat'45'trace'45'of_2282 ::
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3732 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_flat'45'trace'45'of_2282 v0 v1 v2 ~v3 v4 v5 v6 v7 v8
  = du_flat'45'trace'45'of_2282 v0 v1 v2 v4 v5 v6 v7 v8
du_flat'45'trace'45'of_2282 ::
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3732 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
du_flat'45'trace'45'of_2282 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Denotation.Behavior.du_behavior'45'by_50
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_'10214'_'10215'IR_64
         (coe v7)
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_158
            (coe v2)))
      (coe
         du_flat'45'trace'45'fam_2232 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4) (coe v5) (coe v6) (coe v7))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.ir-flat-correct-of
d_ir'45'flat'45'correct'45'of_2302 ::
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3732 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'flat'45'correct'45'of_2302 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.rewrite-preserves-of
d_rewrite'45'preserves'45'of_2322
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.FlatFromObs.rewrite-preserves-of"
-- Once.Adequacy.ArchCorrectness.FlatFromObs.flat-from-obs
d_flat'45'from'45'obs_2332 ::
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3732 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514) ->
  (MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Adequacy.Compile.T_ArchCorrect_48
d_flat'45'from'45'obs_2332 v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8
  = du_flat'45'from'45'obs_2332 v0 v1 v2 v4 v5 v6 v7
du_flat'45'from'45'obs_2332 ::
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3732 ->
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
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514) ->
  MAlonzo.Code.Once.Adequacy.Compile.T_ArchCorrect_48
du_flat'45'from'45'obs_2332 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.C_constructor_118
      (coe du_asm'45'sem_2142 (coe v4))
      (coe
         du_flat'45'trace'45'of_2282 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4) (coe v5) (coe v6))
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.InputAt
d_InputAt_26865 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
