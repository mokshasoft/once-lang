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
d_BeforeFrontier_732 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun
d_CalleeRun_744 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CellAt
d_CellAt_750 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.FlatState
d_FlatState_756 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.FlatSteps
d_FlatSteps_760 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.IRObsCorrectF
d_IRObsCorrectF_772 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_772 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.InputAt
d_InputAt_776 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.MachineRefinesObsF
d_MachineRefinesObsF_782 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                         a13 a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ResultPlace
d_ResultPlace_790 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValidAtWF
d_ValidAtWF_800 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized
d_ValueRealized_802 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                    a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.chain-events
d_chain'45'events_824 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_chain'45'events_824 ~v0 ~v1 v2 = du_chain'45'events_824 v2
du_chain'45'events_824 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_chain'45'events_824 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_chain'45'events_604
      (coe v0) v1 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.enter-call
d_enter'45'call_878 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_enter'45'call_878 ~v0 ~v1 v2 = du_enter'45'call_878 v2
du_enter'45'call_878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_enter'45'call_878 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'call_960 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.evalᴰ
d_eval'7472'_894 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_eval'7472'_894 ~v0 v1 = du_eval'7472'_894 v1
du_eval'7472'_894 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_eval'7472'_894 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_eval'7472'_2660
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.flat-exec-instr
d_flat'45'exec'45'instr_1002 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_1002 ~v0 ~v1 v2
  = du_flat'45'exec'45'instr_1002 v2
du_flat'45'exec'45'instr_1002 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'exec'45'instr_1002 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.bf-mono
d_bf'45'mono_1304 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'mono_1304 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3974
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.cont-alloc
d_cont'45'alloc_1306 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_cont'45'alloc_1306 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3934
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.events
d_events_1308 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_events_1308 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.frame-pres
d_frame'45'pres_1310 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_1310 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.live
d_live_1312 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_1312 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.log
d_log_1314 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_1314 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.mem-pres
d_mem'45'pres_1316 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres_1316 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.no-link
d_no'45'link_1318 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_1318 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.no-ret
d_no'45'ret_1320 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_1320 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.out-mode
d_out'45'mode_1322 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_1322 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3932
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.place
d_place_1324 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_1324 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3950
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.returned
d_returned_1326 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_returned_1326 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.run
d_run_1328 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_run_1328 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3936
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.settle
d_settle_1330 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_1330 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3930
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.steps
d_steps_1332 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  Integer
d_steps_1332 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3928
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.CalleeRun.stops
d_stops_1334 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stops_1334 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.FlatState.falloc
d_falloc_1370 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_falloc_1370 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.FlatState.fclosure
d_fclosure_1372 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_1372 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.FlatState.flink
d_flink_1374 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_1374 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.FlatState.floc
d_floc_1376 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
d_floc_1376 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.FlatState.fpc
d_fpc_1378 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_1378 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.FlatState.fret
d_fret_1380 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_1380 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.MachineRefinesObsF.traces-agree
d_traces'45'agree_1416 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_traces'45'agree_1416 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.MachineRefinesObsF.value-realized
d_value'45'realized_1418 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602
d_value'45'realized_1418 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_3816
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.at-end
d_at'45'end_1480 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_1480 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.bf-mono
d_bf'45'mono_1482 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'mono_1482 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3714
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.cont-alloc
d_cont'45'alloc_1484 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_cont'45'alloc_1484 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3678
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.frame-pres
d_frame'45'pres_1486 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_1486 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.heap-pres
d_heap'45'pres_1488 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'pres_1488 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.live
d_live_1490 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_1490 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.log
d_log_1492 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_1492 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.no-link
d_no'45'link_1494 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_1494 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.no-ret
d_no'45'ret_1496 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_1496 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.out-mode
d_out'45'mode_1498 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_1498 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3676
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.place
d_place_1500 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_1500 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3696
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.run
d_run_1502 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_run_1502 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3680
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.settle
d_settle_1504 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_1504 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3674
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.stack-pres
d_stack'45'pres_1506 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'pres_1506 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.steps
d_steps_1508 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  Integer
d_steps_1508 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3672
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.Core.ValueRealized.stops
d_stops_1510 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stops_1510 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.SMPrimitives.InstrNoHeapWrite
d_InstrNoHeapWrite_1514 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._._+_
d__'43'__2008 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> Integer -> Integer
d__'43'__2008 ~v0 ~v1 = du__'43'__2008
du__'43'__2008 :: Integer -> Integer -> Integer
du__'43'__2008 = coe addInt
-- Once.CCC.Codegen.IRObsCorrect.Out._._≡_
d__'8801'__2026 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.AbstractInstr
d_AbstractInstr_2052 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.AbstractTrace
d_AbstractTrace_2054 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] -> ()
d_AbstractTrace_2054 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.AllocMode
d_AllocMode_2058 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.AllocState
d_AllocState_2060 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics
d_FrameSemantics_2088 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.IR
d_IR_2104 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.IRTy
d_IRTy_2106 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.List
d_List_2118 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.LocState
d_LocState_2120 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.Maybe
d_Maybe_2124 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.StoredValue
d_StoredValue_2152 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.ValueLocation
d_ValueLocation_2160 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.WellFormedFI
d_WellFormedFI_2162 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.fst
d_fst_2278 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_fst_2278 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.snd
d_snd_2280 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_snd_2280 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.readReg
d_readReg_2282 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readReg_2282 ~v0 ~v1 = du_readReg_2282
du_readReg_2282 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readReg_2282 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Out._.sucLoc
d_sucLoc_2310 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_sucLoc_2310 ~v0 ~v1 = du_sucLoc_2310
du_sucLoc_2310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_sucLoc_2310 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 v1
-- Once.CCC.Codegen.IRObsCorrect.Out._.Nat
d_Nat_2340 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out._.⟦_⟧ᴰᴵ
d_'10214'_'10215''7472''7477'_2364 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> ()
d_'10214'_'10215''7472''7477'_2364 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.⟦_⟧TI
d_'10214'_'10215'TI_2366 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IRTy.T_IRTy_6
d_'10214'_'10215'TI_2366 ~v0 ~v1 = du_'10214'_'10215'TI_2366
du_'10214'_'10215'TI_2366 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IRTy.T_IRTy_6
du_'10214'_'10215'TI_2366
  = coe MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
-- Once.CCC.Codegen.IRObsCorrect.Out._.AllocState.block-size
d_block'45'size_2578 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> Integer
d_block'45'size_2578 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_606 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.AllocState.current-frame
d_current'45'frame_2580 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 -> AgdaAny
d_current'45'frame_2580 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.AllocState.frame-slots
d_frame'45'slots_2582 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 -> Integer
d_frame'45'slots_2582 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_600 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.AllocState.next-heap-ref
d_next'45'heap'45'ref_2584 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 -> Integer
d_next'45'heap'45'ref_2584 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.AllocState.next-slot
d_next'45'slot_2586 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 -> Integer
d_next'45'slot_2586 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.AllocState.saved-frames
d_saved'45'frames_2588 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_saved'45'frames_2588 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_598 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics._≟F_
d__'8799'F__3088 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'F__3088 v0
  = coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics._≺_
d__'8826'__3090 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> ()
d__'8826'__3090 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.Frame
d_Frame_3092 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_Frame_3092 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.float-format
d_float'45'format_3094 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28
d_float'45'format_3094 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_float'45'format_126 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.frame-base
d_frame'45'base_3096 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer
d_frame'45'base_3096 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.frame-disjoint-bounded
d_frame'45'disjoint'45'bounded_3098 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_frame'45'disjoint'45'bounded_3098 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.frame-word
d_frame'45'word_3100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> Integer
d_frame'45'word_3100 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'word_110 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.frame-word-pos
d_frame'45'word'45'pos_3102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_frame'45'word'45'pos_3102 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'word'45'pos_112
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.fs-interp
d_fs'45'interp_3104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458
d_fs'45'interp_3104 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.shift-base
d_shift'45'base_3106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shift'45'base_3106 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.shift-frame
d_shift'45'frame_3108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> AgdaAny
d_shift'45'frame_3108 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_108 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.slot-addr
d_slot'45'addr_3110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> Integer
d_slot'45'addr_3110 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_slot'45'addr_94 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.slot-addr-linear
d_slot'45'addr'45'linear_3112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'linear_3112 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.slot-injective
d_slot'45'injective_3114 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_slot'45'injective_3114 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.slot-zero-at-base
d_slot'45'zero'45'at'45'base_3116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'zero'45'at'45'base_3116 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.≺-compare
d_'8826''45'compare_3118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8826''45'compare_3118 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'compare_148
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.≺-irrefl
d_'8826''45'irrefl_3120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''45'irrefl_3120 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out._.FrameSemantics.≺-trans
d_'8826''45'trans_3122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8826''45'trans_3122 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_138 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.LocState.ev-log
d_ev'45'log_3324 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_ev'45'log_3324 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_434 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.LocState.halted
d_halted_3326 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 -> Bool
d_halted_3326 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_432 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.LocState.heapMem
d_heapMem_3328 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_heapMem_3328 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_430 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.LocState.regs
d_regs_3330 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
d_regs_3330 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.LocState.stackMem
d_stackMem_3332 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  AgdaAny ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_stackMem_3332 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_428 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out._.MemOps.readLoc
d_readLoc_3350 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_3350 ~v0 ~v1 = du_readLoc_3350
du_readLoc_3350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_3350 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_666 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.BeforeFrontier
d_BeforeFrontier_3826 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun
d_CalleeRun_3838 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CellAt
d_CellAt_3844 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.FlatState
d_FlatState_3850 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.FlatSteps
d_FlatSteps_3854 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.IRObsCorrectF
d_IRObsCorrectF_3866 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_3866 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.InputAt
d_InputAt_3870 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.MachineRefinesObsF
d_MachineRefinesObsF_3876 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                          a13 a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ResultPlace
d_ResultPlace_3884 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValidAtWF
d_ValidAtWF_3894 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized
d_ValueRealized_3896 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                     a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.chain-events
d_chain'45'events_3918 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_chain'45'events_3918 ~v0 ~v1 v2 = du_chain'45'events_3918 v2
du_chain'45'events_3918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_chain'45'events_3918 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_chain'45'events_604
      (coe v0) v1 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.enter-call
d_enter'45'call_3972 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_enter'45'call_3972 ~v0 ~v1 v2 = du_enter'45'call_3972 v2
du_enter'45'call_3972 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_enter'45'call_3972 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'call_960 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.evalᴰ
d_eval'7472'_3988 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_eval'7472'_3988 ~v0 v1 v2 = du_eval'7472'_3988 v1 v2
du_eval'7472'_3988 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_eval'7472'_3988 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_eval'7472'_2660
      (coe v0) (coe v1)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.flat-exec-instr
d_flat'45'exec'45'instr_4096 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_4096 ~v0 ~v1 v2
  = du_flat'45'exec'45'instr_4096 v2
du_flat'45'exec'45'instr_4096 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'exec'45'instr_4096 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.bf-mono
d_bf'45'mono_4398 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'mono_4398 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3974
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.cont-alloc
d_cont'45'alloc_4400 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_cont'45'alloc_4400 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3934
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.events
d_events_4402 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_events_4402 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.frame-pres
d_frame'45'pres_4404 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_4404 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.live
d_live_4406 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_4406 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.log
d_log_4408 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_4408 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.mem-pres
d_mem'45'pres_4410 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres_4410 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.no-link
d_no'45'link_4412 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_4412 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.no-ret
d_no'45'ret_4414 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_4414 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.out-mode
d_out'45'mode_4416 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_4416 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3932
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.place
d_place_4418 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_4418 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3950
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.returned
d_returned_4420 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_returned_4420 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.run
d_run_4422 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_run_4422 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3936
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.settle
d_settle_4424 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_4424 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3930
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.steps
d_steps_4426 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  Integer
d_steps_4426 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3928
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.CalleeRun.stops
d_stops_4428 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stops_4428 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.FlatState.falloc
d_falloc_4464 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_falloc_4464 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.FlatState.fclosure
d_fclosure_4466 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_4466 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.FlatState.flink
d_flink_4468 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_4468 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.FlatState.floc
d_floc_4470 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
d_floc_4470 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.FlatState.fpc
d_fpc_4472 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_4472 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.FlatState.fret
d_fret_4474 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_4474 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.MachineRefinesObsF.traces-agree
d_traces'45'agree_4510 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_traces'45'agree_4510 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.MachineRefinesObsF.value-realized
d_value'45'realized_4512 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602
d_value'45'realized_4512 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_3816
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.at-end
d_at'45'end_4574 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_4574 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.bf-mono
d_bf'45'mono_4576 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'mono_4576 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3714
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.cont-alloc
d_cont'45'alloc_4578 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_cont'45'alloc_4578 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3678
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.frame-pres
d_frame'45'pres_4580 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_4580 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.heap-pres
d_heap'45'pres_4582 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'pres_4582 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.live
d_live_4584 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_4584 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.log
d_log_4586 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_4586 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.no-link
d_no'45'link_4588 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_4588 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.no-ret
d_no'45'ret_4590 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_4590 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.out-mode
d_out'45'mode_4592 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_4592 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3676
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.place
d_place_4594 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_4594 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3696
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.run
d_run_4596 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_run_4596 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3680
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.settle
d_settle_4598 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_4598 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3674
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.stack-pres
d_stack'45'pres_4600 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'pres_4600 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.steps
d_steps_4602 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  Integer
d_steps_4602 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3672
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ValueRealized.stops
d_stops_4604 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stops_4604 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.SMPrimitives.InstrNoHeapWrite
d_InstrNoHeapWrite_4608 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC.OutSetupPres.b0
d_b0_5112 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_b0_5112 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_b0_5112 v4 v5 v6 v7
du_b0_5112 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_b0_5112 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v1)
      (coe v2) (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v3)
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC.OutSetupPres.b1
d_b1_5114 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_b1_5114 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_b1_5114 v4 v5 v6 v7
du_b1_5114 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_b1_5114 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'save'45'closure_1498
      (coe du_b0_5112 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC.OutSetupPres.b2
d_b2_5116 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_b2_5116 ~v0 ~v1 v2 ~v3 v4 v5 v6 v7 = du_b2_5116 v2 v4 v5 v6 v7
du_b2_5116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_b2_5116 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
      (coe du_b1_5114 (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC.OutSetupPres.b3
d_b3_5118 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_b3_5118 ~v0 ~v1 v2 ~v3 v4 v5 v6 v7 = du_b3_5118 v2 v4 v5 v6 v7
du_b3_5118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_b3_5118 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
      (coe du_b2_5116 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC.OutSetupPres.mem-pres
d_mem'45'pres_5122 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres_5122 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC.OutSetupPres.carry
d_carry_5134 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_carry_5134 v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 v9 v10 ~v11 ~v12 v13
  = du_carry_5134 v0 v1 v2 v4 v5 v6 v7 v9 v10 v13
du_carry_5134 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
du_carry_5134 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5192
      (coe v0) (coe v1) (coe v2) (coe v5) (coe v7) (coe v8) (coe v4)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
         (coe du_b3_5118 (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)))
      (coe v9)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC.OutSetupPres.closure-reg
d_closure'45'reg_5150 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_closure'45'reg_5150 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC.OutSetupPres.input1-b3
d_input1'45'b3_5160 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input1'45'b3_5160 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC.obs-correct-Out
d_obs'45'correct'45'Out_5174 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
d_obs'45'correct'45'Out_5174 v0 v1 v2 v3 ~v4 ~v5 ~v6 v7 v8 ~v9 v10
                             ~v11 ~v12 ~v13 ~v14 ~v15 v16 v17 v18 ~v19 ~v20 v21 v22
  = du_obs'45'correct'45'Out_5174
      v0 v1 v2 v3 v7 v8 v10 v16 v17 v18 v21 v22
du_obs'45'correct'45'Out_5174 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
du_obs'45'correct'45'Out_5174 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v10 of
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'loc_3846 v12 v13 v14
        -> case coe v12 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v16 v17
               -> coe du_stack'45'refuted_5278 (coe v13)
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v16
               -> coe
                    du_go_5348 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                    (coe v6) (coe v7) (coe v8) (coe v9) (coe v16) (coe v11) (coe v13)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.stack-refuted
d_stack'45'refuted_5278 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
d_stack'45'refuted_5278 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22
                        ~v23 ~v24 ~v25 ~v26 v27
  = du_stack'45'refuted_5278 v27
du_stack'45'refuted_5278 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
du_stack'45'refuted_5278 v0
  = coe
      seq (coe v0) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.ν-loc
d_ν'45'loc_5326 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_ν'45'loc_5326 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24
                ~v25
  = du_ν'45'loc_5326 v21
du_ν'45'loc_5326 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_ν'45'loc_5326 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.OSP.b0
d_b0_5330 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_b0_5330 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_b0_5330 v8 v16 v17 v18
du_b0_5330 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_b0_5330 v0 v1 v2 v3
  = coe du_b0_5112 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.OSP.b1
d_b1_5332 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_b1_5332 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_b1_5332 v8 v16 v17 v18
du_b1_5332 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_b1_5332 v0 v1 v2 v3
  = coe du_b1_5114 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.OSP.b2
d_b2_5334 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_b2_5334 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_b2_5334 v2 v8 v16 v17 v18
du_b2_5334 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_b2_5334 v0 v1 v2 v3 v4
  = coe du_b2_5116 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.OSP.b3
d_b3_5336 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_b3_5336 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_b3_5336 v2 v8 v16 v17 v18
du_b3_5336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_b3_5336 v0 v1 v2 v3 v4
  = coe du_b3_5118 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.OSP.carry
d_carry_5338 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_carry_5338 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_carry_5338 v0 v1 v2 v8 v16 v17 v18
du_carry_5338 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
du_carry_5338 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_carry_5134 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) v8 v9 v12
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.OSP.closure-reg
d_closure'45'reg_5340 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_closure'45'reg_5340 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.OSP.input1-b3
d_input1'45'b3_5342 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_input1'45'b3_5342 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.OSP.mem-pres
d_mem'45'pres_5344 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_mem'45'pres_5344 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._.go
d_go_5348 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
d_go_5348 v0 v1 v2 v3 ~v4 ~v5 ~v6 v7 v8 ~v9 v10 ~v11 ~v12 ~v13 ~v14
          ~v15 v16 v17 v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 v25 ~v26 v27
  = du_go_5348 v0 v1 v2 v3 v7 v8 v10 v16 v17 v18 v21 v25 v27
du_go_5348 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
du_go_5348 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'ν'45'susp'45'wf_926 v14 v15 v16 v17 v21 v22 v23 v25
        -> coe
             du_assemble_5434 (coe v0) (coe v1) (coe v3) (coe v15) (coe v2)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v14) (coe v16) (coe v17) (coe v21) (coe v23)
             (coe v25) (coe v23)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.seed-sv-of
d_seed'45'sv'45'of_5372 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_seed'45'sv'45'of_5372 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22
                        ~v23 ~v24 ~v25 ~v26 ~v27 v28 ~v29 ~v30 ~v31 ~v32 ~v33 v34
  = du_seed'45'sv'45'of_5372 v28 v34
du_seed'45'sv'45'of_5372 ::
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_seed'45'sv'45'of_5372 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'ptr_816 v5 v7 v9 v10
        -> coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 (coe v5)
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'inline_828 v6
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_inline'45'sv_600
             (coe v6) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.seed-cell-of
d_seed'45'cell'45'of_5380 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_seed'45'cell'45'of_5380 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.mode-of
d_mode'45'of_5386 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_mode'45'of_5386 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
                  ~v25 ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 v34
  = du_mode'45'of_5386 v34
du_mode'45'of_5386 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
du_mode'45'of_5386 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'ptr_816 v4 v6 v8 v9
        -> coe v6
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'inline_828 v5
        -> coe MAlonzo.Code.Once.IR.C_Heap_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.input-of
d_input'45'of_5392 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832
d_input'45'of_5392 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11
                   ~v12 ~v13 ~v14 ~v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                   v26 ~v27 v28 ~v29 ~v30 ~v31 ~v32 ~v33 v34
  = du_input'45'of_5392 v0 v1 v5 v9 v16 v17 v18 v26 v28 v34
du_input'45'of_5392 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832
du_input'45'of_5392 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'ptr_816 v13 v15 v17 v18
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'loc_3846
             v13
             (coe
                du_carry_5134 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v7) (coe v8) (coe v18))
             v17
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'inline_828 v14
        -> case coe v14 of
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'prim_594 v16
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'reg_3850
                    v16
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'unit_596 v17
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'unit_3852
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.ν-val
d_ν'45'val_5412 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_ν'45'val_5412 ~v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
                ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                v26 v27 v28 ~v29 ~v30 ~v31 ~v32 ~v33
  = du_ν'45'val_5412 v1 v2 v4 v5 v26 v27 v28
du_ν'45'val_5412 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8
du_ν'45'val_5412 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_1052
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v3))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_eval'7472'_2660
         v0 v3 v4 (coe MAlonzo.Code.Once.IRTy.C_ν'45'type_28 (coe v1))
         (coe MAlonzo.Code.Once.IR.C_Ana_120 v2 v5) v6)
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.cinfo
d_cinfo_5414 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_cinfo_5414 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
             ~v13 ~v14 ~v15 v16 v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 ~v25 v26
             v27 v28 v29 ~v30 v31 ~v32 v33
  = du_cinfo_5414 v2 v4 v11 v16 v17 v21 v26 v27 v28 v29 v31 v33
du_cinfo_5414 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cinfo_5414 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_coalgs_4092
      v2 v6 v0 v1 v7 v8 v9 (coe MAlonzo.Code.Once.IR.C_Heap_8) v4
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 (coe v5))
      v3
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'ν'45'susp'45'wf_926
         v6 v1 v7 v8 v9 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) v10 v11)
      erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.j
d_j_5416 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_j_5416 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12 ~v13
         ~v14 ~v15 v16 v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 ~v25 v26 v27
         v28 v29 ~v30 v31 ~v32 v33
  = du_j_5416 v2 v4 v11 v16 v17 v21 v26 v27 v28 v29 v31 v33
du_j_5416 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  Integer
du_j_5416 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         du_cinfo_5414 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11))
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.feq
d_feq_5418 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_feq_5418 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.runner
d_runner_5420 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866
d_runner_5420 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
              ~v13 ~v14 ~v15 v16 v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 ~v25 v26
              v27 v28 v29 ~v30 v31 ~v32 v33
  = du_runner_5420 v2 v4 v11 v16 v17 v21 v26 v27 v28 v29 v31 v33
du_runner_5420 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866
du_runner_5420 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            du_cinfo_5414 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)))
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.code-cell-b3
d_code'45'cell'45'b3_5422 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_code'45'cell'45'b3_5422 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.call-eq
d_call'45'eq_5424 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_call'45'eq_5424 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._.assemble
d_assemble_5434 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
d_assemble_5434 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12 ~v13
                ~v14 ~v15 v16 v17 v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 v25 v26 v27 v28
                v29 ~v30 v31 ~v32 v33 v34
  = du_assemble_5434
      v0 v1 v2 v4 v5 v8 v9 v11 v16 v17 v18 v21 v25 v26 v27 v28 v29 v31
      v33 v34
du_assemble_5434 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
du_assemble_5434 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15 v16 v17 v18 v19
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3820
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3716
         (addInt
            (coe (4 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3928
               (coe
                  du_crun_5448 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                  (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                  (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
                  (coe v19))))
         (MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3930
            (coe
               du_crun_5448 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
               (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
               (coe v19)))
         (MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3932
            (coe
               du_crun_5448 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
               (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
               (coe v19)))
         (MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3934
            (coe
               du_crun_5448 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
               (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
               (coe v19)))
         (coe
            du_run_5478 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
            (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
            (coe v19))
         (\ v20 v21 ->
            coe
              du_place_5492 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
              (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
              (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
              (coe v19) v20)
         (coe
            du_bf'45'mono'45'out_5458 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
            (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v16)
            (coe v17) (coe v18) (coe v19)))
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.nh1
d_nh1_5442 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_nh1_5442 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.nh2
d_nh2_5444 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_nh2_5444 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.nh3
d_nh3_5446 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_nh3_5446 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.crun
d_crun_5448 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866
d_crun_5448 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12 ~v13
            ~v14 ~v15 v16 v17 v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 v25 v26 v27 v28
            v29 ~v30 v31 ~v32 v33 v34
  = du_crun_5448
      v0 v1 v2 v4 v5 v8 v9 v11 v16 v17 v18 v21 v25 v26 v27 v28 v29 v31
      v33 v34
du_crun_5448 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3866
du_crun_5448 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
             v16 v17 v18 v19
  = coe
      du_runner_5420 v2 v3 v7 v8 v9 v11 v13 v14 v15 v16 v17 v18
      (MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call_1340
         (coe v4) (coe v5)
         (coe du_b3_5118 (coe v4) (coe v6) (coe v8) (coe v9) (coe v10)))
      (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
         (coe du_b3_5118 (coe v4) (coe v6) (coe v8) (coe v9) (coe v10)))
      (addInt
         (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86
            (coe du_b3_5118 (coe v4) (coe v6) (coe v8) (coe v9) (coe v10))))
      v12 (coe du_mode'45'of_5386 (coe v19)) erased erased erased erased
      (coe
         du_input'45'of_5392 (coe v0) (coe v1) (coe v4) (coe v6) (coe v8)
         (coe v9) (coe v10) (coe v13) (coe v15) (coe v19))
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.bf-mono-out
d_bf'45'mono'45'out_5458 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_bf'45'mono'45'out_5458 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 v11
                         ~v12 ~v13 ~v14 ~v15 v16 v17 v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 v25
                         v26 v27 v28 v29 ~v30 v31 ~v32 v33 v34 v35 v36 v37
  = du_bf'45'mono'45'out_5458
      v0 v1 v2 v4 v5 v8 v9 v11 v16 v17 v18 v21 v25 v26 v27 v28 v29 v31
      v33 v34 v35 v36 v37
du_bf'45'mono'45'out_5458 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
du_bf'45'mono'45'out_5458 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                          v13 v14 v15 v16 v17 v18 v19 v20 v21 v22
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3974
      (coe
         du_crun_5448 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
         (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
         (coe v19))
      v9 v20 erased v21 v22
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.mem-pres-out
d_mem'45'pres'45'out_5468 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_mem'45'pres'45'out_5468 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.run4
d_run4_5476 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_run4_5476 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
            ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22 ~v23 ~v24 ~v25
            ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34
  = du_run4_5476 v12 v20
du_run4_5476 ::
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
du_run4_5476 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__374
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
         (coe
            v0 (0 :: Integer)
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306)
            erased))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__374
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
            (coe
               v0 (1 :: Integer)
               (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
               erased))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__374
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
               (coe
                  v0 (2 :: Integer)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                  erased))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__374
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282)
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe
                     v0 (3 :: Integer)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282)
                     erased))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_364))))
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.run
d_run_5478 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_run_5478 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12 ~v13 ~v14
           ~v15 v16 v17 v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 v25 v26 v27 v28 v29
           ~v30 v31 ~v32 v33 v34
  = du_run_5478
      v0 v1 v2 v4 v5 v8 v9 v11 v16 v17 v18 v21 v25 v26 v27 v28 v29 v31
      v33 v34
du_run_5478 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
du_run_5478 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
            v16 v17 v18 v19
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45''43''43'_1192
      (coe du_run4_5476 erased erased)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3936
         (coe
            du_crun_5448 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
            (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
            (coe v19)))
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.callFs
d_callFs_5480 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_callFs_5480 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 v9 ~v10 ~v11 ~v12
              ~v13 ~v14 ~v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 ~v26
              ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34
  = du_callFs_5480 v5 v8 v9 v16 v17 v18
du_callFs_5480 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_callFs_5480 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call_1340 (coe v0)
      (coe v1)
      (coe du_b3_5118 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.h-eq
d_h'45'eq_5482 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_h'45'eq_5482 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.RE
d_RE_5484 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_RE_5484 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.st-eq
d_st'45'eq_5486 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_st'45'eq_5486 = erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.place
d_place_5492 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_place_5492 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12 ~v13
             ~v14 ~v15 v16 v17 v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 v25 v26 v27 v28
             v29 ~v30 v31 ~v32 v33 v34 v35 ~v36
  = du_place_5492
      v0 v1 v2 v4 v5 v8 v9 v11 v16 v17 v18 v21 v25 v26 v27 v28 v29 v31
      v33 v34 v35
du_place_5492 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4080 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
du_place_5492 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
              v16 v17 v18 v19 v20
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3950
      (coe
         du_crun_5448 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
         (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
         (coe v19))
      v20 erased
-- Once.CCC.Codegen.IRObsCorrect.Out.OutC._._._.trc
d_trc_5496 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
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
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
d_trc_5496 = erased
