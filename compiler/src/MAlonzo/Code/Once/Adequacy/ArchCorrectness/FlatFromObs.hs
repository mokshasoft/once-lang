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
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.All.Properties
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Adequacy.CPU.Interface
import qualified MAlonzo.Code.Once.Adequacy.FlatEvents
import qualified MAlonzo.Code.Once.Adequacy.SourceTrace
import qualified MAlonzo.Code.Once.CCC.Codegen.BlockLayout
import qualified MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable
import qualified MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas
import qualified MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.Codegen.LabelsUnique
import qualified MAlonzo.Code.Once.CCC.Codegen.ProgramImage
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Behavior
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Target.Arch

-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.BlockRuns
d_BlockRuns_34 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.BlocksAt
d_BlocksAt_38 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_BlocksAt_38 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.IRObsCorrectF
d_IRObsCorrectF_70 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_70 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.InputAt
d_InputAt_74 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.LabelsAt
d_LabelsAt_78 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] -> ()
d_LabelsAt_78 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.MachineRefinesObsF
d_MachineRefinesObsF_80 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                        a13 a14 a15 a16 a17 a18 a19
  = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.SpanAt
d_SpanAt_92 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] -> ()
d_SpanAt_92 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized
d_ValueRealized_100 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                    a14 a15 a16 a17 a18 a19
  = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.blocks
d_blocks_116 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_blocks_116 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 = du_blocks_116 v0
du_blocks_116 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_blocks_116 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_blocks_3478
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.emitted
d_emitted_218 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_emitted_218 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 = du_emitted_218 v0
du_emitted_218 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_emitted_218 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_emitted_3466
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.BlockRuns.closures
d_closures_946 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_closures_946 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_closures_4090
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.BlockRuns.coalgs
d_coalgs_948 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_coalgs_948 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_coalgs_4092
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.BlockRuns.functions
d_functions_950 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_functions_950 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_functions_4094
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.MachineRefinesObsF.traces-agree
d_traces'45'agree_1072 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_traces'45'agree_1072 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.MachineRefinesObsF.value-realized
d_value'45'realized_1074 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602
d_value'45'realized_1074 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_3816
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.at-end
d_at'45'end_1724 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_1724 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.bf-mono
d_bf'45'mono_1726 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'mono_1726 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3714
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.cont-alloc
d_cont'45'alloc_1728 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_cont'45'alloc_1728 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3678
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.frame-pres
d_frame'45'pres_1730 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_1730 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.heap-pres
d_heap'45'pres_1732 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'pres_1732 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.live
d_live_1734 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_1734 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.log
d_log_1736 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_1736 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.no-link
d_no'45'link_1738 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_1738 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.no-ret
d_no'45'ret_1740 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_1740 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.out-mode
d_out'45'mode_1742 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_1742 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3676
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.place
d_place_1744 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_1744 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3696
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.run
d_run_1746 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_run_1746 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3680
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.settle
d_settle_1748 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_1748 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3674
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.stack-pres
d_stack'45'pres_1750 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'pres_1750 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.steps
d_steps_1752 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  Integer
d_steps_1752 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3672
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.ValueRealized.stops
d_stops_1754 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stops_1754 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ir-next-label
d_ir'45'next'45'label_1840 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer -> MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'next'45'label_1840 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_ir'45'next'45'label_1840 v0
du_ir'45'next'45'label_1840 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer -> MAlonzo.Code.Once.IR.T_IR_16 -> Integer
du_ir'45'next'45'label_1840 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'next'45'label_934
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ir-stack-budget
d_ir'45'stack'45'budget_1842 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget_1842 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_ir'45'stack'45'budget_1842 v0
du_ir'45'stack'45'budget_1842 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
du_ir'45'stack'45'budget_1842 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_866
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ir-to-trace
d_ir'45'to'45'trace_1844 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_ir'45'to'45'trace_1844 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_ir'45'to'45'trace_1844 v0
du_ir'45'to'45'trace_1844 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_ir'45'to'45'trace_1844 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_848
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.NoThunks
d_NoThunks_1938 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_NoThunks_1938 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.BlockRuns
d_BlockRuns_2650 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.BlocksAt
d_BlocksAt_2654 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_BlocksAt_2654 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectF
d_IRObsCorrectF_2658 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_2658 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.LabelsAt
d_LabelsAt_2660 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] -> ()
d_LabelsAt_2660 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.MachineRefinesObsF
d_MachineRefinesObsF_2662 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                          a13 a14 a15 a16 a17 a18
  = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.SpanAt
d_SpanAt_2666 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] -> ()
d_SpanAt_2666 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized
d_ValueRealized_2668 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                     a14 a15 a16 a17 a18
  = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.blocks
d_blocks_2672 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_blocks_2672 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_blocks_2672 v0
du_blocks_2672 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_blocks_2672 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_blocks_3478
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.emitted
d_emitted_2674 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_emitted_2674 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_emitted_2674 v0
du_emitted_2674 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_emitted_2674 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_emitted_3466
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.BlockRuns.closures
d_closures_2680 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_closures_2680 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_closures_4090
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.BlockRuns.coalgs
d_coalgs_2682 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_coalgs_2682 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_coalgs_4092
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.BlockRuns.functions
d_functions_2684 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_functions_2684 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_functions_4094
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.MachineRefinesObsF.traces-agree
d_traces'45'agree_2688 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_traces'45'agree_2688 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.MachineRefinesObsF.value-realized
d_value'45'realized_2690 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602
d_value'45'realized_2690 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_3816
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.at-end
d_at'45'end_2694 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_2694 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.bf-mono
d_bf'45'mono_2696 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'mono_2696 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3714
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.cont-alloc
d_cont'45'alloc_2698 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_cont'45'alloc_2698 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3678
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.frame-pres
d_frame'45'pres_2700 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_2700 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.heap-pres
d_heap'45'pres_2702 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'pres_2702 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.live
d_live_2704 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_2704 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.log
d_log_2706 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_2706 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.no-link
d_no'45'link_2708 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_2708 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.no-ret
d_no'45'ret_2710 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_2710 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.out-mode
d_out'45'mode_2712 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_2712 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3676
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.place
d_place_2714 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_2714 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3696
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.run
d_run_2716 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_run_2716 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3680
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.settle
d_settle_2718 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_2718 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3674
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.stack-pres
d_stack'45'pres_2720 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'pres_2720 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.steps
d_steps_2722 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  Integer
d_steps_2722 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3672
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValueRealized.stops
d_stops_2724 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stops_2724 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.FlatState
d_FlatState_2728 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.FlatState.falloc
d_falloc_2750 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_falloc_2750 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.FlatState.fclosure
d_fclosure_2752 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_2752 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.FlatState.flink
d_flink_2754 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_2754 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.FlatState.floc
d_floc_2756 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
d_floc_2756 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.FlatState.fpc
d_fpc_2758 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_2758 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.FlatState.fret
d_fret_2760 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_2760 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.AllSlotStable
d_AllSlotStable_2774 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] -> ()
d_AllSlotStable_2774 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.BeforeFrontier
d_BeforeFrontier_2786 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-alloc
d_entry'45'alloc_2830 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_entry'45'alloc_2830 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7
  = du_entry'45'alloc_2830 v5 v7
du_entry'45'alloc_2830 ::
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_entry'45'alloc_2830 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_608 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v1)
      (coe (0 :: Integer)) (coe (1 :: Integer))
      (coe (\ v2 -> 0 :: Integer))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-loc
d_entry'45'loc_2836 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_entry'45'loc_2836 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_entry'45'loc_2836
du_entry'45'loc_2836 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_entry'45'loc_2836
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
            (coe (0 :: Integer)))
         (coe (0 :: Integer)))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-regs
d_entry'45'regs_2838 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
d_entry'45'regs_2838 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_entry'45'regs_2838
du_entry'45'regs_2838 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
du_entry'45'regs_2838
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
d_entry'45's_2840 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
d_entry'45's_2840 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_entry'45's_2840
du_entry'45's_2840 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
du_entry'45's_2840
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_436
      (coe du_entry'45'regs_2838)
      (coe (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      (coe (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-ns
d_entry'45'ns_2850 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_entry'45'ns_2850 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_entry'45'ns_2850
du_entry'45'ns_2850 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_entry'45'ns_2850 = coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-bf
d_entry'45'bf_2854 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_entry'45'bf_2854 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_entry'45'bf_2854
du_entry'45'bf_2854 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_entry'45'bf_2854
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_686
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-nh
d_entry'45'nh_2856 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'nh_2856 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.main-span
d_main'45'span_2860 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_main'45'span_2860 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.main-labels
d_main'45'labels_2874 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_main'45'labels_2874 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-no-thunks
d_entry'45'no'45'thunks_2888 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny
d_entry'45'no'45'thunks_2888 v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7
  = du_entry'45'no'45'thunks_2888 v0 v3 v7
du_entry'45'no'45'thunks_2888 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny
du_entry'45'no'45'thunks_2888 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.LabelsUnique.d_entry'45'noThunks_1302
      (coe v0) (coe v1) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_866
         (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.top-pre
d_top'45'pre_2894 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_top'45'pre_2894 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_top'45'pre_2894 v0 v1 v7
du_top'45'pre_2894 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_top'45'pre_2894 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2242
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_866
               (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2))))
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_emitted_3466
            (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
            (coe (0 :: Integer)) (coe v2))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_top'45'done_30
                     (coe v0)
                     (coe
                        MAlonzo.Code.Once.Denotation.Program.C_irProgram_390 (coe v1)
                        (coe v2)))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_top'45'done_30
                        (coe v0)
                        (coe
                           MAlonzo.Code.Once.Denotation.Program.C_irProgram_390 (coe v1)
                           (coe v2)))))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.main-blocks
d_main'45'blocks_2900 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_main'45'blocks_2900 v0 v1 ~v2 v3 ~v4 ~v5 ~v6 v7
  = du_main'45'blocks_2900 v0 v1 v3 v7
du_main'45'blocks_2900 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_main'45'blocks_2900 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.BlockLayout.du_blocks'45'at_254
      (coe du_top'45'pre_2894 (coe v0) (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_blocks_3478
         (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
         (coe (0 :: Integer)) (coe v3))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.BlockLayout.du_missBefore'45'from_400
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_blocks_3478
            (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
            (coe (0 :: Integer)) (coe v3))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.LabelsUnique.d_top'45'noThunks_1320
            (coe v0) (coe v2) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v3)
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_866
               (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v3))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_top'45'done_30
               (coe v0)
               (coe
                  MAlonzo.Code.Once.Denotation.Program.C_irProgram_390 (coe v1)
                  (coe v3)))))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.image
d_image_2904 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_image_2904 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_image_2904 v0 v1 v7
du_image_2904 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_image_2904 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_program'45'image_42
      (coe v0)
      (coe
         MAlonzo.Code.Once.Denotation.Program.C_irProgram_390 (coe v1)
         (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.BlockRunsT
d_BlockRunsT_2908 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 -> ()
d_BlockRunsT_2908 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.span-prefix
d_span'45'prefix_2920 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_span'45'prefix_2920 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.blocks-prefix
d_blocks'45'prefix_2944 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_blocks'45'prefix_2944 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_blocks'45'prefix_2944 v9 v10
du_blocks'45'prefix_2944 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_blocks'45'prefix_2944 v0 v1
  = case coe v0 of
      []
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    seq (coe v5)
                    (case coe v1 of
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v8 v9
                         -> case coe v8 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                -> coe
                                     seq (coe v11)
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                              erased))
                                        (coe du_blocks'45'prefix_2944 (coe v3) (coe v9)))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatFromObs.rest
d_rest_2970 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_rest_2970 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_rest_2970 v0 v1 v7
du_rest_2970 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_rest_2970 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
            (coe
               MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_top'45'done_30
               (coe v0)
               (coe
                  MAlonzo.Code.Once.Denotation.Program.C_irProgram_390 (coe v1)
                  (coe v2)))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_top'45'done_30
                  (coe v0)
                  (coe
                     MAlonzo.Code.Once.Denotation.Program.C_irProgram_390 (coe v1)
                     (coe v2)))))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_blocks'45'layout_2350
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_blocks_3478
               (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
               (coe (0 :: Integer)) (coe v2))))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.image-assoc
d_image'45'assoc_2976 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_image'45'assoc_2976 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-span
d_entry'45'span_2986 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'span_2986 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-labels
d_entry'45'labels_3000 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'labels_3000 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-blocks
d_entry'45'blocks_3014 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_entry'45'blocks_3014 v0 v1 ~v2 v3 ~v4 ~v5 ~v6 v7
  = du_entry'45'blocks_3014 v0 v1 v3 v7
du_entry'45'blocks_3014 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_entry'45'blocks_3014 v0 v1 v2 v3
  = coe
      du_blocks'45'prefix_2944
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_blocks_3478
         (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
         (coe (0 :: Integer)) (coe v3))
      (coe du_main'45'blocks_2900 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.fns-slot-stable
d_fns'45'slot'45'stable_3024 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_fns'45'slot'45'stable_3024 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8
  = du_fns'45'slot'45'stable_3024 v3 v7 v8
du_fns'45'slot'45'stable_3024 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_fns'45'slot'45'stable_3024 v0 v1 v2
  = case coe v2 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v3 v4
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236
                      (coe
                         MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v3)))
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget'45'from_896
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v3))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v3))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v3))
                         (coe v1)
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v3)))))
                (let v5
                       = MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v3) in
                 coe
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace'45'lab_924
                      (coe v5)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v3))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v3))
                      (coe v1)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v3)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'to'45'trace'45'lab'45'slot'45'stable_940
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v3))
                   (coe v0)
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v3))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v3))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v3))
                   (coe v1)))
             (coe
                du_fns'45'slot'45'stable_3024 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v1)
                   (coe v3))
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatFromObs.image-slot-stable
d_image'45'slot'45'stable_3036 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_image'45'slot'45'stable_3036 v0 v1 ~v2 v3 ~v4 ~v5 ~v6 v7
  = du_image'45'slot'45'stable_3036 v0 v1 v3 v7
du_image'45'slot'45'stable_3036 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_image'45'slot'45'stable_3036 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_link'45'top_2376
            (coe
               MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_top'45'done_30
               (coe v0)
               (coe
                  MAlonzo.Code.Once.Denotation.Program.C_irProgram_390 (coe v1)
                  (coe v3)))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'unit_842 v0
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) v3))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_ir'45'to'45'trace'45'top'45'slot'45'stable_954
            (coe v0) (coe v2) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v3))
         (coe
            du_fns'45'slot'45'stable_3024 (coe v2)
            (coe
               addInt (coe (1 :: Integer))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'next'45'label_934
                  (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                  (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
                  (coe v3)))
            (coe v1)))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.start-flat
d_start'45'flat_3040 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_start'45'flat_3040 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_start'45'flat_3040 v5
du_start'45'flat_3040 ::
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_start'45'flat_3040 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
      (coe du_entry'45's_2840)
      (coe du_entry'45'alloc_2830 (coe v0) (coe (0 :: Integer)))
      (coe (0 :: Integer))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72
         (coe (0 :: Integer)))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Once.Adequacy.ArchCorrectness.FlatFromObs.main-flat
d_main'45'flat_3042 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_main'45'flat_3042 v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7
  = du_main'45'flat_3042 v0 v3 v5 v7
du_main'45'flat_3042 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_main'45'flat_3042 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'thunk_1274 (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_866
         (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v3))
      (coe du_start'45'flat_3040 (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-witness
d_entry'45'witness_3052 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
    Integer ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786) ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
d_entry'45'witness_3052 v0 v1 ~v2 v3 ~v4 v5 ~v6 v7 v8 v9 v10
  = du_entry'45'witness_3052 v0 v1 v3 v5 v7 v8 v9 v10
du_entry'45'witness_3052 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
    Integer ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786) ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
du_entry'45'witness_3052 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      v5 (0 :: Integer) (0 :: Integer)
      (coe du_image_2904 (coe v0) (coe v1) (coe v4)) (1 :: Integer)
      (coe
         du_image'45'slot'45'stable_3036 (coe v0) (coe v1) (coe v2)
         (coe v4))
      (coe v6 v4) erased
      (coe du_entry'45'blocks_3014 (coe v0) (coe v1) (coe v2) (coe v4))
      erased (coe MAlonzo.Code.Once.IR.C_Stack_6)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
         (coe du_main'45'flat_3042 (coe v0) (coe v2) (coe v3) (coe v4)))
      (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
         (coe du_main'45'flat_3042 (coe v0) (coe v2) (coe v3) (coe v4)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72
         (coe (0 :: Integer)))
      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26) erased
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'unit_3852)
      v7
-- Once.Adequacy.ArchCorrectness.FlatFromObs.IOC
d_IOC_3062 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 -> ()
d_IOC_3062 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.σFS
d_σFS_3064 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_σFS_3064 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 = du_σFS_3064 v3
du_σFS_3064 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_σFS_3064 v0
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.d_sig_464
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-vr
d_entry'45'vr_3078 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   AgdaAny ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
    Integer ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786) ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602
d_entry'45'vr_3078 v0 v1 ~v2 v3 ~v4 v5 ~v6 v7 v8 v9 v10 v11
  = du_entry'45'vr_3078 v0 v1 v3 v5 v7 v8 v9 v10 v11
du_entry'45'vr_3078 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   AgdaAny ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
    Integer ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786) ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602
du_entry'45'vr_3078 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_3816
      (coe
         du_entry'45'witness_3052 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4)
         (coe
            v6 (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16) v4
            (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
         (coe v7) (coe v8))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.flat-trace-fam
d_flat'45'trace'45'fam_3092 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   AgdaAny ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
    Integer ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786) ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_flat'45'trace'45'fam_3092 v0 v1 ~v2 v3 ~v4 v5 ~v6 v7 v8 v9 v10
                            v11
  = du_flat'45'trace'45'fam_3092 v0 v1 v3 v5 v7 v8 v9 v10 v11
du_flat'45'trace'45'fam_3092 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   AgdaAny ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
    Integer ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786) ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_flat'45'trace'45'fam_3092 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Data.List.Base.du_take_530 (coe v8)
      (coe
         MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_464 (coe v2)
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3672
               (coe
                  du_entry'45'vr_3078 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6)
                  (coe v7) (coe v4) (coe v5) (coe v8))))
         (coe du_image_2904 (coe v0) (coe v1) (coe v6))
         (coe du_start'45'flat_3040 (coe v3)))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.ir-flat-correct-fam
d_ir'45'flat'45'correct'45'fam_3114 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   AgdaAny ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
    Integer ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786) ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'flat'45'correct'45'fam_3114 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.flat-main
d_flat'45'main_3128 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   AgdaAny ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
    Integer ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786) ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_flat'45'main_3128 v0 v1 ~v2 v3 ~v4 v5 ~v6 v7 v8 v9 v10
  = du_flat'45'main_3128 v0 v1 v3 v5 v7 v8 v9 v10
du_flat'45'main_3128 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   AgdaAny ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
    Integer ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786) ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
du_flat'45'main_3128 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Denotation.Behavior.du_behavior'45'by_50
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_'10214'_'10215'IR_252
         (coe
            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
            (coe
               MAlonzo.Code.Once.Denotation.Program.C_irProgram_390 (coe v1)
               (coe v6)))
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_166 (coe v2))
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v2)))
      (coe
         du_flat'45'trace'45'fam_3092 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4) (coe v5) (coe v6) (coe v7))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.ir-flat-correct-main
d_ir'45'flat'45'correct'45'main_3150 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   AgdaAny ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
    Integer ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786) ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'flat'45'correct'45'main_3150 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.InputAt
d_InputAt_30533 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
