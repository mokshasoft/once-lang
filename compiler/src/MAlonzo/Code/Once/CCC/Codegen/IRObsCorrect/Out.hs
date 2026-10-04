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

module MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Out where

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
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.FlatEvents
import qualified MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas
import qualified MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Machine.SMPrimitives
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Codegen.IRObsCorrect.Out._.Σ
d_Σ_11 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.AbstractReg
d_AbstractReg_13 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Bool
d_Bool_17 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.⊤
d_'8868'_19 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.BeforeFrontier
d_BeforeFrontier_730 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun
d_CalleeRun_742 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CellAt
d_CellAt_748 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.FlatState
d_FlatState_754 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.FlatSteps
d_FlatSteps_758 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.IRObsCorrectF
d_IRObsCorrectF_770 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_770 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.InputAt
d_InputAt_774 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.MachineRefinesObsF
d_MachineRefinesObsF_780 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                         a13 a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ResultPlace
d_ResultPlace_788 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValidAtWF
d_ValidAtWF_798 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized
d_ValueRealized_800 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                    a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.chain-events
d_chain'45'events_822 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_chain'45'events_822 ~v0 ~v1 v2 = du_chain'45'events_822 v2
du_chain'45'events_822 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_chain'45'events_822 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_chain'45'events_604
      (coe v0) v1 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.enter-call
d_enter'45'call_876 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_enter'45'call_876 ~v0 ~v1 v2 = du_enter'45'call_876 v2
du_enter'45'call_876 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_enter'45'call_876 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'call_960 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.evalᴰ
d_eval'7472'_892 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_eval'7472'_892 ~v0 v1 = du_eval'7472'_892 v1
du_eval'7472'_892 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_eval'7472'_892 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_eval'7472'_2658
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.flat-exec-instr
d_flat'45'exec'45'instr_1000 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_1000 ~v0 ~v1 v2
  = du_flat'45'exec'45'instr_1000 v2
du_flat'45'exec'45'instr_1000 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'exec'45'instr_1000 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.bf-mono
d_bf'45'mono_1302 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'mono_1302 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3972
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.cont-alloc
d_cont'45'alloc_1304 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_cont'45'alloc_1304 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3932
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.events
d_events_1306 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_events_1306 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.frame-pres
d_frame'45'pres_1308 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_1308 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.live
d_live_1310 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_1310 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.log
d_log_1312 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_1312 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.mem-pres
d_mem'45'pres_1314 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres_1314 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.no-link
d_no'45'link_1316 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_1316 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.no-ret
d_no'45'ret_1318 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_1318 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.out-mode
d_out'45'mode_1320 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_1320 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3930
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.place
d_place_1322 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_1322 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3948
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.returned
d_returned_1324 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_returned_1324 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.run
d_run_1326 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_run_1326 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3934
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.settle
d_settle_1328 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_1328 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3928
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.steps
d_steps_1330 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  Integer
d_steps_1330 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3926
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.stops
d_stops_1332 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stops_1332 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.FlatState.falloc
d_falloc_1368 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_falloc_1368 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.FlatState.fclosure
d_fclosure_1370 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_1370 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.FlatState.flink
d_flink_1372 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_1372 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.FlatState.floc
d_floc_1374 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_1374 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.FlatState.fpc
d_fpc_1376 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_1376 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.FlatState.fret
d_fret_1378 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_1378 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.MachineRefinesObsF.traces-agree
d_traces'45'agree_1414 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_traces'45'agree_1414 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.MachineRefinesObsF.value-realized
d_value'45'realized_1416 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600
d_value'45'realized_1416 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_3814
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.at-end
d_at'45'end_1478 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_1478 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.bf-mono
d_bf'45'mono_1480 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'mono_1480 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3712
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.cont-alloc
d_cont'45'alloc_1482 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_cont'45'alloc_1482 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3676
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.frame-pres
d_frame'45'pres_1484 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_1484 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.heap-pres
d_heap'45'pres_1486 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'pres_1486 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.live
d_live_1488 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_1488 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.log
d_log_1490 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_1490 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.no-link
d_no'45'link_1492 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_1492 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.no-ret
d_no'45'ret_1494 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_1494 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.out-mode
d_out'45'mode_1496 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_1496 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3674
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.place
d_place_1498 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_1498 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3694
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.run
d_run_1500 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_run_1500 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3678
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.settle
d_settle_1502 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_1502 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.stack-pres
d_stack'45'pres_1504 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'pres_1504 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.steps
d_steps_1506 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer
d_steps_1506 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3670
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.stops
d_stops_1508 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stops_1508 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.SMPrimitives.InstrNoHeapWrite
d_InstrNoHeapWrite_1512 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._._+_
d__'43'__1946 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> Integer -> Integer
d__'43'__1946 ~v0 ~v1 = du__'43'__1946
du__'43'__1946 :: Integer -> Integer -> Integer
du__'43'__1946 = coe addInt
-- Once.CCC.Codegen.IRObsCorrect.Out._._≡_
d__'8801'__1964 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.AbstractInstr
d_AbstractInstr_1990 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.AbstractTrace
d_AbstractTrace_1992 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] -> ()
d_AbstractTrace_1992 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.AllocMode
d_AllocMode_1996 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.AllocState
d_AllocState_1998 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics
d_FrameSemantics_2026 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.IR
d_IR_2042 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.IRTy
d_IRTy_2044 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.List
d_List_2056 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.LocState
d_LocState_2058 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Maybe
d_Maybe_2062 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.StoredValue
d_StoredValue_2090 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.ValueLocation
d_ValueLocation_2098 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.WellFormedFI
d_WellFormedFI_2100 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.fst
d_fst_2216 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_fst_2216 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.snd
d_snd_2218 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_snd_2218 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.readReg
d_readReg_2220 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readReg_2220 ~v0 ~v1 = du_readReg_2220
du_readReg_2220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readReg_2220 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Out._.sucLoc
d_sucLoc_2248 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_sucLoc_2248 ~v0 ~v1 = du_sucLoc_2248
du_sucLoc_2248 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_sucLoc_2248 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 v1
-- Once.CCC.Codegen.IRObsCorrect.Out._.Nat
d_Nat_2278 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.⟦_⟧ᴰᴵ
d_'10214'_'10215''7472''7477'_2302 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> ()
d_'10214'_'10215''7472''7477'_2302 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.⟦_⟧TI
d_'10214'_'10215'TI_2304 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IRTy.T_IRTy_6
d_'10214'_'10215'TI_2304 ~v0 ~v1 = du_'10214'_'10215'TI_2304
du_'10214'_'10215'TI_2304 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IRTy.T_IRTy_6
du_'10214'_'10215'TI_2304
  = coe MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
-- Once.CCC.Codegen.IRObsCorrect.Out._.AllocState.block-size
d_block'45'size_2516 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> Integer
d_block'45'size_2516 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_594 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.AllocState.current-frame
d_current'45'frame_2518 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 -> AgdaAny
d_current'45'frame_2518 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.AllocState.frame-slots
d_frame'45'slots_2520 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 -> Integer
d_frame'45'slots_2520 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_588 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.AllocState.next-heap-ref
d_next'45'heap'45'ref_2522 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 -> Integer
d_next'45'heap'45'ref_2522 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.AllocState.next-slot
d_next'45'slot_2524 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 -> Integer
d_next'45'slot_2524 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_590 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.AllocState.saved-frames
d_saved'45'frames_2526 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_saved'45'frames_2526 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_586 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics._≟F_
d__'8799'F__3026 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'F__3026 v0
  = coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics._≺_
d__'8826'__3028 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> ()
d__'8826'__3028 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.Frame
d_Frame_3030 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_Frame_3030 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.float-format
d_float'45'format_3032 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28
d_float'45'format_3032 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_float'45'format_126 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.frame-base
d_frame'45'base_3034 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer
d_frame'45'base_3034 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.frame-disjoint-bounded
d_frame'45'disjoint'45'bounded_3036 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_frame'45'disjoint'45'bounded_3036 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.frame-word
d_frame'45'word_3038 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> Integer
d_frame'45'word_3038 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'word_110 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.frame-word-pos
d_frame'45'word'45'pos_3040 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_frame'45'word'45'pos_3040 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'word'45'pos_112
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.fs-interp
d_fs'45'interp_3042 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458
d_fs'45'interp_3042 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.shift-base
d_shift'45'base_3044 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shift'45'base_3044 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.shift-frame
d_shift'45'frame_3046 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> AgdaAny
d_shift'45'frame_3046 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_108 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.slot-addr
d_slot'45'addr_3048 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> Integer
d_slot'45'addr_3048 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_slot'45'addr_94 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.slot-addr-linear
d_slot'45'addr'45'linear_3050 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'linear_3050 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.slot-injective
d_slot'45'injective_3052 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_slot'45'injective_3052 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.slot-zero-at-base
d_slot'45'zero'45'at'45'base_3054 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'zero'45'at'45'base_3054 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.≺-compare
d_'8826''45'compare_3056 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8826''45'compare_3056 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'compare_148
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.≺-irrefl
d_'8826''45'irrefl_3058 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''45'irrefl_3058 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.≺-trans
d_'8826''45'trans_3060 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8826''45'trans_3060 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_138 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.LocState.ev-log
d_ev'45'log_3262 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_ev'45'log_3262 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_424 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.LocState.halted
d_halted_3264 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
d_halted_3264 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_422 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.LocState.heapMem
d_heapMem_3266 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_heapMem_3266 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_420 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.LocState.regs
d_regs_3268 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
d_regs_3268 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.LocState.stackMem
d_stackMem_3270 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_stackMem_3270 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_418 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.MemOps.readLoc
d_readLoc_3288 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_3288 ~v0 ~v1 = du_readLoc_3288
du_readLoc_3288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_3288 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.BeforeFrontier
d_BeforeFrontier_3764 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun
d_CalleeRun_3776 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CellAt
d_CellAt_3782 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.FlatState
d_FlatState_3788 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.FlatSteps
d_FlatSteps_3792 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.IRObsCorrectF
d_IRObsCorrectF_3804 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_3804 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.InputAt
d_InputAt_3808 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.MachineRefinesObsF
d_MachineRefinesObsF_3814 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                          a13 a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ResultPlace
d_ResultPlace_3822 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValidAtWF
d_ValidAtWF_3832 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized
d_ValueRealized_3834 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                     a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.chain-events
d_chain'45'events_3856 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_chain'45'events_3856 ~v0 ~v1 v2 = du_chain'45'events_3856 v2
du_chain'45'events_3856 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_chain'45'events_3856 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_chain'45'events_604
      (coe v0) v1 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.enter-call
d_enter'45'call_3910 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_enter'45'call_3910 ~v0 ~v1 v2 = du_enter'45'call_3910 v2
du_enter'45'call_3910 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_enter'45'call_3910 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'call_960 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.evalᴰ
d_eval'7472'_3926 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_eval'7472'_3926 ~v0 v1 v2 = du_eval'7472'_3926 v1 v2
du_eval'7472'_3926 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_eval'7472'_3926 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_eval'7472'_2658
      (coe v0) (coe v1)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.flat-exec-instr
d_flat'45'exec'45'instr_4034 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_4034 ~v0 ~v1 v2
  = du_flat'45'exec'45'instr_4034 v2
du_flat'45'exec'45'instr_4034 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'exec'45'instr_4034 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.bf-mono
d_bf'45'mono_4336 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'mono_4336 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3972
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.cont-alloc
d_cont'45'alloc_4338 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_cont'45'alloc_4338 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3932
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.events
d_events_4340 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_events_4340 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.frame-pres
d_frame'45'pres_4342 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_4342 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.live
d_live_4344 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_4344 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.log
d_log_4346 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_4346 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.mem-pres
d_mem'45'pres_4348 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres_4348 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.no-link
d_no'45'link_4350 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_4350 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.no-ret
d_no'45'ret_4352 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_4352 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.out-mode
d_out'45'mode_4354 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_4354 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3930
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.place
d_place_4356 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_4356 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3948
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.returned
d_returned_4358 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_returned_4358 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.run
d_run_4360 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_run_4360 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3934
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.settle
d_settle_4362 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_4362 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3928
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.steps
d_steps_4364 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  Integer
d_steps_4364 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3926
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.stops
d_stops_4366 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stops_4366 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.FlatState.falloc
d_falloc_4402 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_falloc_4402 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.FlatState.fclosure
d_fclosure_4404 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_4404 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.FlatState.flink
d_flink_4406 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_4406 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.FlatState.floc
d_floc_4408 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_4408 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.FlatState.fpc
d_fpc_4410 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_4410 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.FlatState.fret
d_fret_4412 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_4412 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.MachineRefinesObsF.traces-agree
d_traces'45'agree_4448 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_traces'45'agree_4448 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.MachineRefinesObsF.value-realized
d_value'45'realized_4450 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600
d_value'45'realized_4450 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_3814
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.at-end
d_at'45'end_4512 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_4512 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.bf-mono
d_bf'45'mono_4514 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'mono_4514 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3712
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.cont-alloc
d_cont'45'alloc_4516 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_cont'45'alloc_4516 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3676
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.frame-pres
d_frame'45'pres_4518 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_4518 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.heap-pres
d_heap'45'pres_4520 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'pres_4520 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.live
d_live_4522 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_4522 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.log
d_log_4524 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_4524 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.no-link
d_no'45'link_4526 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_4526 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.no-ret
d_no'45'ret_4528 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_4528 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.out-mode
d_out'45'mode_4530 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_4530 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3674
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.place
d_place_4532 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_4532 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3694
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.run
d_run_4534 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_run_4534 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3678
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.settle
d_settle_4536 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_4536 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.stack-pres
d_stack'45'pres_4538 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'pres_4538 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.steps
d_steps_4540 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer
d_steps_4540 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3670
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.stops
d_stops_4542 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stops_4542 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.SMPrimitives.InstrNoHeapWrite
d_InstrNoHeapWrite_4546 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC.OutSetupPres.b0
d_b0_4990 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_b0_4990 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_b0_4990 v4 v5 v6 v7
du_b0_4990 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_b0_4990 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v1)
      (coe v2) (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v3)
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC.OutSetupPres.b1
d_b1_4992 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_b1_4992 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_b1_4992 v4 v5 v6 v7
du_b1_4992 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_b1_4992 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'save'45'closure_1498
      (coe du_b0_4990 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC.OutSetupPres.b2
d_b2_4994 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_b2_4994 ~v0 ~v1 v2 ~v3 v4 v5 v6 v7 = du_b2_4994 v2 v4 v5 v6 v7
du_b2_4994 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_b2_4994 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244)
      (coe du_b1_4992 (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC.OutSetupPres.b3
d_b3_4996 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_b3_4996 ~v0 ~v1 v2 ~v3 v4 v5 v6 v7 = du_b3_4996 v2 v4 v5 v6 v7
du_b3_4996 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_b3_4996 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
      (coe du_b2_4994 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC.OutSetupPres.mem-pres
d_mem'45'pres_5000 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres_5000 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC.OutSetupPres.carry
d_carry_5012 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_carry_5012 v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 v9 v10 ~v11 ~v12 v13
  = du_carry_5012 v0 v1 v2 v4 v5 v6 v7 v9 v10 v13
du_carry_5012 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
du_carry_5012 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5192
      (coe v0) (coe v1) (coe v2) (coe v5) (coe v7) (coe v8) (coe v4)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
         (coe du_b3_4996 (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)))
      (coe v9)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC.OutSetupPres.closure-reg
d_closure'45'reg_5028 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_closure'45'reg_5028 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC.OutSetupPres.input1-b3
d_input1'45'b3_5038 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input1'45'b3_5038 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC.obs-correct-Out
d_obs'45'correct'45'Out_5052 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
d_obs'45'correct'45'Out_5052 v0 v1 v2 v3 ~v4 ~v5 ~v6 v7 v8 ~v9 v10
                             ~v11 ~v12 ~v13 ~v14 ~v15 v16 v17 v18 ~v19 ~v20 v21 v22
  = du_obs'45'correct'45'Out_5052
      v0 v1 v2 v3 v7 v8 v10 v16 v17 v18 v21 v22
du_obs'45'correct'45'Out_5052 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
du_obs'45'correct'45'Out_5052 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v10 of
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'loc_3844 v12 v13 v14
        -> case coe v12 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v16 v17
               -> coe du_stack'45'refuted_5156 (coe v13)
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v16
               -> coe
                    du_go_5226 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                    (coe v6) (coe v7) (coe v8) (coe v9) (coe v16) (coe v11) (coe v13)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.stack-refuted
d_stack'45'refuted_5156 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
d_stack'45'refuted_5156 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22
                        ~v23 ~v24 ~v25 ~v26 v27
  = du_stack'45'refuted_5156 v27
du_stack'45'refuted_5156 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
du_stack'45'refuted_5156 v0
  = coe
      seq (coe v0) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ν-loc
d_ν'45'loc_5204 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_ν'45'loc_5204 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24
                ~v25
  = du_ν'45'loc_5204 v21
du_ν'45'loc_5204 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_ν'45'loc_5204 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.OSP.b0
d_b0_5208 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_b0_5208 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_b0_5208 v8 v16 v17 v18
du_b0_5208 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_b0_5208 v0 v1 v2 v3
  = coe du_b0_4990 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.OSP.b1
d_b1_5210 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_b1_5210 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_b1_5210 v8 v16 v17 v18
du_b1_5210 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_b1_5210 v0 v1 v2 v3
  = coe du_b1_4992 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.OSP.b2
d_b2_5212 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_b2_5212 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_b2_5212 v2 v8 v16 v17 v18
du_b2_5212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_b2_5212 v0 v1 v2 v3 v4
  = coe du_b2_4994 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.OSP.b3
d_b3_5214 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_b3_5214 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_b3_5214 v2 v8 v16 v17 v18
du_b3_5214 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_b3_5214 v0 v1 v2 v3 v4
  = coe du_b3_4996 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.OSP.carry
d_carry_5216 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_carry_5216 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_carry_5216 v0 v1 v2 v8 v16 v17 v18
du_carry_5216 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
du_carry_5216 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_carry_5012 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) v8 v9 v12
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.OSP.closure-reg
d_closure'45'reg_5218 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_closure'45'reg_5218 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.OSP.input1-b3
d_input1'45'b3_5220 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input1'45'b3_5220 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.OSP.mem-pres
d_mem'45'pres_5222 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres_5222 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.go
d_go_5226 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
d_go_5226 v0 v1 v2 v3 ~v4 ~v5 ~v6 v7 v8 ~v9 v10 ~v11 ~v12 ~v13 ~v14
          ~v15 v16 v17 v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 v25 ~v26 v27
  = du_go_5226 v0 v1 v2 v3 v7 v8 v10 v16 v17 v18 v21 v25 v27
du_go_5226 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
du_go_5226 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'ν'45'susp'45'wf_926 v14 v15 v16 v17 v21 v22 v23 v25
        -> coe
             du_assemble_5312 (coe v0) (coe v1) (coe v3) (coe v15) (coe v2)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v14) (coe v16) (coe v17) (coe v21) (coe v23)
             (coe v25) (coe v23)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.seed-sv-of
d_seed'45'sv'45'of_5250 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_seed'45'sv'45'of_5250 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22
                        ~v23 ~v24 ~v25 ~v26 ~v27 v28 ~v29 ~v30 ~v31 ~v32 ~v33 v34
  = du_seed'45'sv'45'of_5250 v28 v34
du_seed'45'sv'45'of_5250 ::
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_seed'45'sv'45'of_5250 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'ptr_816 v5 v7 v9 v10
        -> coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 (coe v5)
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'inline_828 v6
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_inline'45'sv_600
             (coe v6) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.seed-cell-of
d_seed'45'cell'45'of_5258 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seed'45'cell'45'of_5258 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.mode-of
d_mode'45'of_5264 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_mode'45'of_5264 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
                  ~v25 ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 v34
  = du_mode'45'of_5264 v34
du_mode'45'of_5264 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
du_mode'45'of_5264 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'ptr_816 v4 v6 v8 v9
        -> coe v6
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'inline_828 v5
        -> coe MAlonzo.Code.Once.IR.C_Heap_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.input-of
d_input'45'of_5270 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830
d_input'45'of_5270 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11
                   ~v12 ~v13 ~v14 ~v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                   v26 ~v27 v28 ~v29 ~v30 ~v31 ~v32 ~v33 v34
  = du_input'45'of_5270 v0 v1 v5 v9 v16 v17 v18 v26 v28 v34
du_input'45'of_5270 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830
du_input'45'of_5270 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'ptr_816 v13 v15 v17 v18
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'loc_3844
             v13
             (coe
                du_carry_5012 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v7) (coe v8) (coe v18))
             v17
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'inline_828 v14
        -> case coe v14 of
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'prim_594 v16
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'reg_3848
                    v16
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'unit_596 v17
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'unit_3850
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.ν-val
d_ν'45'val_5290 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8
d_ν'45'val_5290 ~v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
                ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                v26 v27 v28 ~v29 ~v30 ~v31 ~v32 ~v33
  = du_ν'45'val_5290 v1 v2 v4 v5 v26 v27 v28
du_ν'45'val_5290 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8
du_ν'45'val_5290 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_1052
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v3))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_eval'7472'_2658
         v0 v3 v4 (coe MAlonzo.Code.Once.IRTy.C_ν'45'type_28 (coe v1))
         (coe MAlonzo.Code.Once.IR.C_Ana_120 v2 v5) v6)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.cinfo
d_cinfo_5292 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cinfo_5292 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
             ~v13 ~v14 ~v15 v16 v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 ~v25 v26
             v27 v28 v29 ~v30 v31 ~v32 v33
  = du_cinfo_5292 v2 v4 v11 v16 v17 v21 v26 v27 v28 v29 v31 v33
du_cinfo_5292 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cinfo_5292 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_coalgs_4090
      v2 v6 v0 v1 v7 v8 v9 (coe MAlonzo.Code.Once.IR.C_Heap_8) v4
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 (coe v5))
      v3
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'ν'45'susp'45'wf_926
         v6 v1 v7 v8 v9 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) v10 v11)
      erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.j
d_j_5294 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  Integer
d_j_5294 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12 ~v13
         ~v14 ~v15 v16 v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 ~v25 v26 v27
         v28 v29 ~v30 v31 ~v32 v33
  = du_j_5294 v2 v4 v11 v16 v17 v21 v26 v27 v28 v29 v31 v33
du_j_5294 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  Integer
du_j_5294 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         du_cinfo_5292 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11))
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.feq
d_feq_5296 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_feq_5296 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.runner
d_runner_5298 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864
d_runner_5298 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
              ~v13 ~v14 ~v15 v16 v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 ~v25 v26
              v27 v28 v29 ~v30 v31 ~v32 v33
  = du_runner_5298 v2 v4 v11 v16 v17 v21 v26 v27 v28 v29 v31 v33
du_runner_5298 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864
du_runner_5298 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            du_cinfo_5292 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)))
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.code-cell-b3
d_code'45'cell'45'b3_5300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'cell'45'b3_5300 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.call-eq
d_call'45'eq_5302 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_call'45'eq_5302 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.assemble
d_assemble_5312 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
d_assemble_5312 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12 ~v13
                ~v14 ~v15 v16 v17 v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 v25 v26 v27 v28
                v29 ~v30 v31 ~v32 v33 v34
  = du_assemble_5312
      v0 v1 v2 v4 v5 v8 v9 v11 v16 v17 v18 v21 v25 v26 v27 v28 v29 v31
      v33 v34
du_assemble_5312 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
du_assemble_5312 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15 v16 v17 v18 v19
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3818
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3714
         (addInt
            (coe (4 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3926
               (coe
                  du_crun_5326 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                  (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                  (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
                  (coe v19))))
         (MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3928
            (coe
               du_crun_5326 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
               (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
               (coe v19)))
         (MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3930
            (coe
               du_crun_5326 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
               (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
               (coe v19)))
         (MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3932
            (coe
               du_crun_5326 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
               (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
               (coe v19)))
         (coe
            du_run_5356 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
            (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
            (coe v19))
         (\ v20 v21 ->
            coe
              du_place_5370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
              (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
              (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
              (coe v19) v20)
         (coe
            du_bf'45'mono'45'out_5336 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
            (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v16)
            (coe v17) (coe v18) (coe v19)))
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.nh1
d_nh1_5320 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh1_5320 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.nh2
d_nh2_5322 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh2_5322 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.nh3
d_nh3_5324 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh3_5324 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.crun
d_crun_5326 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864
d_crun_5326 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12 ~v13
            ~v14 ~v15 v16 v17 v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 v25 v26 v27 v28
            v29 ~v30 v31 ~v32 v33 v34
  = du_crun_5326
      v0 v1 v2 v4 v5 v8 v9 v11 v16 v17 v18 v21 v25 v26 v27 v28 v29 v31
      v33 v34
du_crun_5326 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3864
du_crun_5326 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
             v16 v17 v18 v19
  = coe
      du_runner_5298 v2 v3 v7 v8 v9 v11 v13 v14 v15 v16 v17 v18
      (MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call_1340
         (coe v4) (coe v5)
         (coe du_b3_4996 (coe v4) (coe v6) (coe v8) (coe v9) (coe v10)))
      (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
         (coe du_b3_4996 (coe v4) (coe v6) (coe v8) (coe v9) (coe v10)))
      (addInt
         (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86
            (coe du_b3_4996 (coe v4) (coe v6) (coe v8) (coe v9) (coe v10))))
      v12 (coe du_mode'45'of_5264 (coe v19)) erased erased erased erased
      (coe
         du_input'45'of_5270 (coe v0) (coe v1) (coe v4) (coe v6) (coe v8)
         (coe v9) (coe v10) (coe v13) (coe v15) (coe v19))
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.bf-mono-out
d_bf'45'mono'45'out_5336 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'mono'45'out_5336 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 v11
                         ~v12 ~v13 ~v14 ~v15 v16 v17 v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 v25
                         v26 v27 v28 v29 ~v30 v31 ~v32 v33 v34 v35 v36 v37
  = du_bf'45'mono'45'out_5336
      v0 v1 v2 v4 v5 v8 v9 v11 v16 v17 v18 v21 v25 v26 v27 v28 v29 v31
      v33 v34 v35 v36 v37
du_bf'45'mono'45'out_5336 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_bf'45'mono'45'out_5336 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                          v13 v14 v15 v16 v17 v18 v19 v20 v21 v22
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3972
      (coe
         du_crun_5326 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
         (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
         (coe v19))
      v9 v20 erased v21 v22
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.mem-pres-out
d_mem'45'pres'45'out_5346 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres'45'out_5346 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.run4
d_run4_5354 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_run4_5354 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
            ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22 ~v23 ~v24 ~v25
            ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34
  = du_run4_5354 v12 v20
du_run4_5354 ::
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
du_run4_5354 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__374
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
         (coe
            v0 (0 :: Integer)
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294)
            erased))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__374
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
            (coe
               v0 (1 :: Integer)
               (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244)
               erased))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__374
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
               (coe
                  v0 (2 :: Integer)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
                  erased))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__374
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270)
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe
                     v0 (3 :: Integer)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270)
                     erased))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_364))))
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.run
d_run_5356 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_run_5356 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12 ~v13 ~v14
           ~v15 v16 v17 v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 v25 v26 v27 v28 v29
           ~v30 v31 ~v32 v33 v34
  = du_run_5356
      v0 v1 v2 v4 v5 v8 v9 v11 v16 v17 v18 v21 v25 v26 v27 v28 v29 v31
      v33 v34
du_run_5356 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
du_run_5356 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
            v16 v17 v18 v19
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45''43''43'_1192
      (coe du_run4_5354 erased erased)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3934
         (coe
            du_crun_5326 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
            (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
            (coe v19)))
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.callFs
d_callFs_5358 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_callFs_5358 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 v9 ~v10 ~v11 ~v12
              ~v13 ~v14 ~v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 ~v26
              ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34
  = du_callFs_5358 v5 v8 v9 v16 v17 v18
du_callFs_5358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_callFs_5358 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call_1340 (coe v0)
      (coe v1)
      (coe du_b3_4996 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.h-eq
d_h'45'eq_5360 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_h'45'eq_5360 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.RE
d_RE_5362 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_RE_5362 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.st-eq
d_st'45'eq_5364 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_st'45'eq_5364 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.place
d_place_5370 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_5370 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12 ~v13
             ~v14 ~v15 v16 v17 v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 v25 v26 v27 v28
             v29 ~v30 v31 ~v32 v33 v34 v35 ~v36
  = du_place_5370
      v0 v1 v2 v4 v5 v8 v9 v11 v16 v17 v18 v21 v25 v26 v27 v28 v29 v31
      v33 v34 v35
du_place_5370 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
du_place_5370 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
              v16 v17 v18 v19 v20
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3948
      (coe
         du_crun_5326 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
         (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
         (coe v19))
      v20 erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.trc
d_trc_5374 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trc_5374 = erased
